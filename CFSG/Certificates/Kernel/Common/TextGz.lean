module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.HarnessGz

open Lean Elab Command

open CFSG.KC.Gz in
elab "#kc_text_gz " sId:ident path:str size:num hash:num : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let some txt := String.fromUTF8? b | throwError "#kc_text_gz: {path.getString} is not UTF-8"
  let sN := (← getCurrNamespace) ++ sId.getId
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (forceExpose := true) <| .defnDecl
      { name := sN, levelParams := [], type := mkConst ``String, value := mkStrLit txt,
        hints := .regular 0, safety := .safe }
    compileDecls #[sN]
