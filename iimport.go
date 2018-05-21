// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Indexed package import.
// See cmd/compile/internal/gc/iexport.go for the export data format.

package main

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"io"
)

type intReader struct {
	*bytes.Reader
	path string
}

func (r *intReader) int64() int64 {
	i, err := binary.ReadVarint(r.Reader)
	if err != nil {
		panic(fmt.Errorf("import %q: read varint error: %v", r.path, err))
	}
	return i
}

func (r *intReader) uint64() uint64 {
	i, err := binary.ReadUvarint(r.Reader)
	if err != nil {
		panic(fmt.Errorf("import %q: read varint error: %v", r.path, err))
	}
	return i
}

const predeclReserved = 32

type itag uint64

const (
	// Types
	definedType itag = iota
	pointerType
	sliceType
	arrayType
	chanType
	mapType
	signatureType
	structType
	interfaceType
)

func (p *gc_bin_importer) parse_import(fset *token.FileSet, imports map[string]string, data []byte, path string, pfc *package_file_cache, callback func(string, ast.Decl)) {
	p.callback = callback

	r := &intReader{bytes.NewReader(data), path}

	version := r.uint64()
	switch version {
	case 0:
	default:
		panic(fmt.Errorf("cannot import %q: unknown iexport format version %d", path, version))
	}

	sLen := int64(r.uint64())
	dLen := int64(r.uint64())

	whence, _ := r.Seek(0, io.SeekCurrent)
	stringData := data[whence : whence+sLen]
	declData := data[whence+sLen : whence+sLen+dLen]
	r.Seek(sLen+dLen, io.SeekCurrent)

	p.ipath = path

	p.stringData = stringData
	p.stringCache = make(map[uint64]string)
	p.pkgCache = make(map[uint64]string)

	p.declData = declData
	p.pkgIndex = make(map[string]map[string]uint64)
	p.typCache = make(map[uint64]ast.Expr)

	p.fake = fakeFileSet{
		fset:  fset,
		files: make(map[string]*token.File),
	}

	p.pfc = pfc

	for i, pt := range predeclared {
		p.typCache[uint64(i)] = pt
	}

	pkgList := make([]string, r.uint64())
	for i := range pkgList {
		pkgPathOff := r.uint64()
		pkgPath := p.stringAt(pkgPathOff)
		pkgName := p.stringAt(r.uint64())
		_ = r.uint64() // package height; unused by go/types

		if pkgPath == "" {
			pkgPath = path
		}
		pkg := imports[pkgPath]
		var fullName string
		if path != "" {
			fullName = "!" + pkgPath + "!" + pkgName
			p.pfc.add_package_to_scope(fullName, pkgPath)
		} else {
			fullName = "!" + p.pfc.name + "!" + pkgName
		}

		p.pkgCache[pkgPathOff] = pkg

		nameIndex := make(map[string]uint64)
		for nSyms := r.uint64(); nSyms > 0; nSyms-- {
			name := p.stringAt(r.uint64())
			nameIndex[name] = r.uint64()
		}

		p.pkgIndex[pkg] = nameIndex
		pkgList[i] = pkg
	}

	// localpkg := pkgList[0]
	//
	// names := make([]string, 0, len(p.pkgIndex[localpkg]))
	// for name := range p.pkgIndex[localpkg] {
	// 	names = append(names, name)
	// }
	// sort.Strings(names)
	// for _, name := range names {
	// 	p.doDecl(localpkg, name)
	// }
	//
	// for _, typ := range p.interfaceList {
	// 	// typ.Complete()
	// 	typ.Incomplete = false
	// }
	//
	// // record all referenced packages as imports
	// list := append(([]string)(nil), pkgList[1:]...)
	// sort.Sort(byPath(list))
	// localpkg.SetImports(list)
	//
	// // package was imported completely and without errors
	// localpkg.MarkComplete()
	//
	// consumed, _ := r.Seek(0, io.SeekCurrent)
	// return int(consumed), localpkg, nil
}

type gc_bin_importer struct {
	ipath string

	stringData  []byte
	stringCache map[uint64]string
	pkgCache    map[uint64]string

	declData []byte
	pkgIndex map[string]map[string]uint64
	typCache map[uint64]ast.Expr

	fake          fakeFileSet
	interfaceList []*ast.InterfaceType

	pfc      *package_file_cache
	callback func(pkg string, decl ast.Decl)
}

func (p *gc_bin_importer) doDecl(pkg string, name string) {
	// See if we've already imported this declaration.
	// if obj := pkg.Scope.Lookup(name); obj != nil {
	// 	return
	// }
	apkg := ast.Package{Name: pkg}
	if obj := apkg.Scope.Lookup(name); obj != nil {
		return
	}

	off, ok := p.pkgIndex[pkg][name]
	if !ok {
		panic(fmt.Errorf("%v.%v not in index", pkg, name))
	}

	r := &importReader{p: p, currPkg: pkg}
	r.declReader.Reset(p.declData[off:])

	r.obj(name)
}

func (p *gc_bin_importer) stringAt(off uint64) string {
	if s, ok := p.stringCache[off]; ok {
		return s
	}

	slen, n := binary.Uvarint(p.stringData[off:])
	if n <= 0 {
		panic(fmt.Errorf("varint failed"))
	}
	spos := off + uint64(n)
	s := string(p.stringData[spos : spos+slen])
	p.stringCache[off] = s
	return s
}

func (p *gc_bin_importer) pkgAt(off uint64) *ast.Package {
	if pkg, ok := p.pkgCache[off]; ok {
		return &ast.Package{Name: pkg}
	}
	path := p.stringAt(off)
	panic(fmt.Errorf("missing package %q in %q", path, p.ipath))
	return nil
}

func (p *gc_bin_importer) typAt(off uint64, base *types.Named) ast.Expr {
	if t, ok := p.typCache[off]; ok && (base == nil || !isInterface(t)) {
		return t
	}

	if off < predeclReserved {
		panic(fmt.Errorf("predeclared type missing from cache: %v", off))
	}

	r := &importReader{p: p}
	r.declReader.Reset(p.declData[off-predeclReserved:])
	t := r.doType(base)

	if base == nil || !isInterface(t) {
		p.typCache[off] = t
	}
	return t
}

type importReader struct {
	p          *gc_bin_importer
	declReader bytes.Reader
	currPkg    string
	prevFile   string
	prevLine   int64
}

func (r *importReader) obj(name string) {
	tag := r.byte()
	pos := r.pos()

	switch tag {
	case 'A':
		typ := r.typ()

		// r.declare(types.NewTypeName(pos, r.currPkg, name, typ))
		r.p.callback(r.currPkg, &ast.GenDecl{
			Tok:    token.TYPE,
			TokPos: pos,
			Specs:  []ast.Spec{typeAliasSpec(name, typ)},
		})

	case 'C':
		typ, val := r.value()

		// r.declare(types.NewConst(pos, r.currPkg, name, typ, val))
		r.p.callback(r.currPkg, &ast.GenDecl{
			Tok: token.CONST,
			Specs: []ast.Spec{
				&ast.ValueSpec{
					Names:  []*ast.Ident{ast.NewIdent(name)},
					Type:   typ,
					Values: []ast.Expr{&ast.BasicLit{Kind: token.INT, Value: "0"}},
				},
			},
		})

	case 'F':
		// sig := r.signature(nil)
		params := r.paramList()
		results := r.paramList()

		// r.declare(types.NewFunc(pos, r.currPkg, name, sig))
		r.p.callback(name, &ast.FuncDecl{
			Name: &ast.Ident{Name: name},
			Type: &ast.FuncType{Params: params, Results: results},
		})

	case 'T':
		// Types can be recursive. We need to setup a stub
		// declaration before recursing.
		// obj := types.NewTypeName(pos, r.currPkg, name, nil)
		obj := &ast.GenDecl{
			Tok: token.TYPE,
			Specs: []ast.Spec{
				&ast.TypeSpec{
					Name:   ast.NewIdent(name),
					Assign: pos,
				},
			},
		}
		// named := types.NewNamed(obj, nil, nil)
		// r.declare(r.currPkg, obj)
		r.p.callback(r.currPkg, obj)

		// underlying := r.p.typAt(r.uint64(), named).Underlying()
		// named.SetUnderlying(underlying)
		//
		// if !isInterface(underlying) {
		// 	for n := r.uint64(); n > 0; n-- {
		// 		mpos := r.pos()
		// 		mname := r.ident()
		// 		recv := r.param()
		// 		msig := r.signature(recv)
		//
		// 		named.AddMethod(types.NewFunc(mpos, r.currPkg, mname, msig))
		// 	}
		// }

	case 'V':
		typ := r.typ()

		// r.declare(types.NewVar(pos, r.currPkg, name, typ))
		r.p.callback(r.currPkg, &ast.GenDecl{
			Tok: token.VAR,
			Specs: []ast.Spec{
				&ast.ValueSpec{
					Names: []*ast.Ident{ast.NewIdent(name)},
					Type:  typ,
				},
			},
		})

	default:
		panic(fmt.Errorf("unexpected tag: %v", tag))
	}
}

func (r *importReader) declare(obj ast.Object) {
	// obj.Pkg().Scope().Insert(obj)
}

func (r *importReader) value() (typ ast.Expr, val constant.Value) {
	typ = r.typ()

	// switch b := typ.Underlying().(*types.Basic); b.Info() & types.IsConstType {
	switch b := typ.(*ast.BasicLit); {
	// case types.IsBoolean:
	case b.Kind.IsOperator():
		val = constant.MakeBool(r.bool())

	// case types.IsString:
	case b.Kind.IsLiteral():
		val = constant.MakeString(r.string())

	// case types.IsInteger:
	case b.Kind == token.INT:
		val = r.mpint(b)

	// case types.IsFloat:
	case b.Kind == token.FLOAT:
		val = r.mpfloat(b)

	// case types.IsComplex:
	case b.Kind == token.IMAG:
		re := r.mpfloat(b)
		im := r.mpfloat(b)
		val = constant.BinaryOp(re, token.ADD, constant.MakeImag(im))

	default:
		panic(fmt.Errorf("unexpected type %v", typ)) // panics
		panic("unreachable")
	}

	return
}

func intSize(b *ast.BasicLit) (signed bool, maxBytes uint) {
	if (b.Info() & types.IsUntyped) != 0 {
		return true, 64
	}

	switch b.Kind() {
	case types.Float32, types.Complex64:
		return true, 3
	case types.Float64, types.Complex128:
		return true, 7
	}

	signed = (b.Info() & types.IsUnsigned) == 0
	switch b.Kind() {
	case types.Int8, types.Uint8:
		maxBytes = 1
	case types.Int16, types.Uint16:
		maxBytes = 2
	case types.Int32, types.Uint32:
		maxBytes = 4
	default:
		maxBytes = 8
	}

	return
}

func (r *importReader) mpint(b *ast.BasicLit) constant.Value {
	signed, maxBytes := intSize(b)

	maxSmall := 256 - maxBytes
	if signed {
		maxSmall = 256 - 2*maxBytes
	}
	if maxBytes == 1 {
		maxSmall = 256
	}

	n, _ := r.declReader.ReadByte()
	if uint(n) < maxSmall {
		v := int64(n)
		if signed {
			v >>= 1
			if n&1 != 0 {
				v = ^v
			}
		}
		return constant.MakeInt64(v)
	}

	v := -n
	if signed {
		v = -(n &^ 1) >> 1
	}
	if v < 1 || uint(v) > maxBytes {
		panic(fmt.Errorf("weird decoding: %v, %v => %v", n, signed, v))
	}

	buf := make([]byte, v)
	io.ReadFull(&r.declReader, buf)

	// convert to little endian
	// TODO(gri) go/constant should have a more direct conversion function
	//           (e.g., once it supports a big.Float based implementation)
	for i, j := 0, len(buf)-1; i < j; i, j = i+1, j-1 {
		buf[i], buf[j] = buf[j], buf[i]
	}

	x := constant.MakeFromBytes(buf)
	if signed && n&1 != 0 {
		x = constant.UnaryOp(token.SUB, x, 0)
	}
	return x
}

func (r *importReader) mpfloat(b *ast.BasicLit) constant.Value {
	x := r.mpint(b)
	if constant.Sign(x) == 0 {
		return x
	}

	exp := r.int64()
	switch {
	case exp > 0:
		x = constant.Shift(x, token.SHL, uint(exp))
	case exp < 0:
		d := constant.Shift(constant.MakeInt64(1), token.SHL, uint(-exp))
		x = constant.BinaryOp(x, token.QUO, d)
	}
	return x
}

func (r *importReader) ident() string {
	return r.string()
}

func (r *importReader) qualifiedIdent() (string, string) {
	name := r.string()
	pkg := r.pkg()
	return pkg, name
}

func (r *importReader) pos() token.Pos {
	delta := r.int64()
	if delta != deltaNewFile {
		r.prevLine += delta
	} else if l := r.int64(); l == -1 {
		r.prevLine += deltaNewFile
	} else {
		r.prevFile = r.string()
		r.prevLine = l
	}

	if r.prevFile == "" && r.prevLine == 0 {
		return token.NoPos
	}

	return r.p.fake.pos(r.prevFile, int(r.prevLine))
}

func (r *importReader) typ() ast.Expr {
	return r.p.typAt(r.uint64(), nil)
}

func isInterface(t ast.Expr) bool {
	_, ok := t.(*ast.Interface)
	return ok
}

func (r *importReader) pkg() *types.Package { return r.p.pkgAt(r.uint64()) }
func (r *importReader) string() string      { return r.p.stringAt(r.uint64()) }

func (r *importReader) doType(base *types.Named) ast.Expr {
	switch k := r.kind(); k {
	default:
		panic(fmt.Errorf("unexpected kind tag in %q: %v", r.p.ipath, k))
		return nil

	case definedType:
		pkg, name := r.qualifiedIdent()
		r.p.doDecl(pkg, name)
		return pkg.Scope().Lookup(name).(*types.TypeName).Type()
	case pointerType:
		return types.NewPointer(r.typ())
	case sliceType:
		return types.NewSlice(r.typ())
	case arrayType:
		n := r.uint64()
		return types.NewArray(r.typ(), int64(n))
	case chanType:
		dir := chanDir(int(r.uint64()))
		return types.NewChan(dir, r.typ())
	case mapType:
		return types.NewMap(r.typ(), r.typ())
	case signatureType:
		r.currPkg = r.pkg()
		return r.signature(nil)

	case structType:
		r.currPkg = r.pkg()

		fields := make([]*types.Var, r.uint64())
		tags := make([]string, len(fields))
		for i := range fields {
			fpos := r.pos()
			fname := r.ident()
			ftyp := r.typ()
			emb := r.bool()
			tag := r.string()

			fields[i] = types.NewField(fpos, r.currPkg, fname, ftyp, emb)
			tags[i] = tag
		}
		return types.NewStruct(fields, tags)

	case interfaceType:
		r.currPkg = r.pkg()

		embeddeds := make([]*types.Named, r.uint64())
		for i := range embeddeds {
			_ = r.pos()
			embeddeds[i] = r.typ().(*types.Named)
		}

		methods := make([]*types.Func, r.uint64())
		for i := range methods {
			mpos := r.pos()
			mname := r.ident()

			// TODO(mdempsky): Matches bimport.go, but I
			// don't agree with this.
			var recv *types.Var
			if base != nil {
				recv = types.NewVar(token.NoPos, r.currPkg, "", base)
			}

			msig := r.signature(recv)
			methods[i] = types.NewFunc(mpos, r.currPkg, mname, msig)
		}

		typ := types.NewInterface(methods, embeddeds)
		r.p.interfaceList = append(r.p.interfaceList, typ)
		return typ
	}
}

func (r *importReader) kind() itag {
	return itag(r.uint64())
}

// func (r *importReader) signature(recv *types.Var) *types.Signature {
// 	params := r.paramList()
// 	results := r.paramList()
// 	variadic := params.Len() > 0 && r.bool()
// 	return types.NewSignature(recv, params, results, variadic)
// }

func (r *importReader) paramList() *ast.FieldList {
	xs := make([]*ast.Field, r.uint64())
	for i := range xs {
		xs[i] = r.param()
	}
	return &ast.FieldList{List: xs}
}

func (r *importReader) param() *ast.Field {
	_ = r.pos()
	name := r.ident()
	typ := r.typ()
	return &ast.Field{
		Names: []*ast.Ident{ast.NewIdent(name)},
		Type:  typ,
	}
}

func (r *importReader) bool() bool {
	return r.uint64() != 0
}

func (r *importReader) int64() int64 {
	n, err := binary.ReadVarint(&r.declReader)
	if err != nil {
		panic(fmt.Errorf("readVarint: %v", err))
	}
	return n
}

func (r *importReader) uint64() uint64 {
	n, err := binary.ReadUvarint(&r.declReader)
	if err != nil {
		panic(fmt.Errorf("readUvarint: %v", err))
	}
	return n
}

func (r *importReader) byte() byte {
	x, err := r.declReader.ReadByte()
	if err != nil {
		panic(fmt.Errorf("declReader.ReadByte: %v", err))
	}
	return x
}
