module

public import CFSG.Certificates.Kernel.Bounds.Checks
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Bounds.Checks

open Lean Elab Command

public section

namespace CFSG.Certificates.KB

@[expose] noncomputable def alphaScan (amap : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun g acc => Prod.rec (motive := fun _ => Nat × Nat) (fun cnt mask =>
      Prod.mk (Bool.rec (Nat.succ cnt) cnt (Nat.beq (byte amap g) (nat_lit 0)))
        (Nat.lor mask (Nat.shiftLeft (nat_lit 1) (byte amap g)))) acc) (nat_lit 256)

@[expose] noncomputable def alphaOk (amap L : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun cnt mask =>
    Bool.rec false
      (Nat.beq (Nat.lor mask (nat_lit 1)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.succ cnt)) (nat_lit 1)))
      (Nat.beq (Nat.shiftLeft cnt (nat_lit 1)) L)) (alphaScan amap)

@[expose] noncomputable def hdrOk (inv L eps amap : Nat) : Bool :=
  Bool.rec false (Bool.rec false (alphaOk amap L) (invOk inv L)) (Nat.beq eps L)

@[expose] noncomputable def idAmap (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun g acc => Nat.lor acc (Nat.shiftLeft (Nat.succ g) (Nat.shiftLeft g (nat_lit 3)))) n

@[expose] noncomputable def topOk (amap n : Nat) : Bool := Nat.beq amap (idAmap n)

@[expose] noncomputable def linkOk (amap' : Nat) (ws : List (List (Nat × Bool))) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun cnt _ =>
    Nat.beq
      (List.rec (motive := fun _ => Nat → Nat) (fun j => j)
        (fun w _ ih j => Prod.rec (motive := fun _ => Nat) (fun e ok =>
          Bool.rec (ih bad)
            (Bool.rec (ih bad) (ih (Nat.succ j))
              (Nat.beq e (Nat.lor (nat_lit 1) (Nat.shiftLeft (Nat.shiftLeft j (nat_lit 1)) (nat_lit 24)))))
            ok) (sEnc amap' w)) ws (nat_lit 0))
      cnt) (alphaScan amap')

@[expose] noncomputable def powEnc (e k : Nat) : Nat :=
  Nat.lor (Nat.mul (Nat.land e (nat_lit 16777215)) k)
    (Nat.shiftLeft
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun _ acc => Nat.lor
          (Nat.shiftLeft acc (Nat.shiftLeft (Nat.land e (nat_lit 16777215)) (nat_lit 3)))
          (Nat.shiftRight e (nat_lit 24))) k)
      (nat_lit 24))

@[expose] noncomputable def powOk (amap : Nat) (ws : List (List (Nat × Bool))) (k : Nat)
    (rels : List (List (Nat × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w tl _ =>
      Bool.rec false
        (Bool.rec false
          (Prod.rec (motive := fun _ => Bool) (fun e ok =>
            Bool.rec false (hasRel amap (powEnc e k) rels) ok) (sEnc amap w))
          (Nat.ble (nat_lit 1) k))
        (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) tl)) ws

@[expose] noncomputable def relIn (amap : Nat) (w : List (Nat × Bool))
    (rels : List (List (Nat × Bool))) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun e ok => Bool.rec false (hasRel amap e rels) ok) (sEnc amap w)

end CFSG.Certificates.KB

namespace CFSG.Certificates.KB.Hdr

open CFSG.Certificates.KB.Load

meta def boolT (_ : Unit := ()) : Expr := mkConst ``Bool
meta def pairT (_ : Unit := ()) : Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) natT boolT
meta def wordT (_ : Unit := ()) : Expr := mkApp (mkConst ``List [Level.zero]) pairT
meta def wordsT (_ : Unit := ()) : Expr := mkApp (mkConst ``List [Level.zero]) wordT

meta def listE (α : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) α x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) α)

meta def letterE (g : Nat) (b : Bool) : Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) natT boolT (lit g)
    (mkConst (if b then ``Bool.true else ``Bool.false))

meta def parseWords (s : String) : Except String (List (List (Nat × Bool))) := do
  let mut out := []
  for w in (s.splitOn " ").filter (· ≠ "") do
    let mut word := []
    for x in w.splitOn "," do
      match x.toInt? with
      | some i =>
        if i == 0 then throw s!"letter 0 in {w}"
        word := word ++ [((i.natAbs - 1), decide (0 < i))]
      | none => throw s!"letter {x} in {w}"
    out := out ++ [word]
  return out

meta def wordsE (ws : List (List (Nat × Bool))) : Expr :=
  listE wordT (ws.map fun w => listE pairT (w.map fun (g, b) => letterE g b))

meta def addCheck (name : Name) (c : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <|
    { name, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) boolT c (mkConst ``Bool.true),
      value := reflBoolTrue }

end CFSG.Certificates.KB.Hdr

open CFSG.Certificates.KB.Load CFSG.Certificates.KB.Hdr in
elab "#kb_table " ns:ident t:ident p:ident "include_bytes" path:str size:num hash:num amap:num
    rels:ident subs:str : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  let h := CFSG.Certificates.KB.Checks.parseHeader b
  let T := ns.getId ++ t.getId
  let D := `CFSG.KBData ++ p.getId
  let R := rels.getId
  unless (← getEnv).contains R do throwError "unknown relator list {R}"
  let ws ← match parseWords subs.getString with
    | .ok ws => pure ws
    | .error e => throwError "subgroup words: {e}"
  let am := mkConst (T ++ `amap)
  let kb := CFSG.Certificates.KB.Checks.kb
  withSync do
    addDef (T ++ `amap) natT (lit amap.getNat)
    addDef (T ++ `words) wordsT (wordsE ws)
    addDef (T ++ `N) natT (lit (h.get "N"))
    addCheck (T ++ `hdr_ok)
      (mkAppN (kb "hdrOk") #[lit h.inv, lit (h.get "L"), lit (h.get "EPS"), am])
    addCheck (T ++ `rels_ok)
      (mkAppN (kb "relsOk") #[mkConst (D ++ `R), lit (h.get "R"), am, mkConst R])
    addCheck (T ++ `subs_ok)
      (mkAppN (kb "subsOk") #[mkConst (D ++ `S), lit (h.get "K"), am, mkConst (T ++ `words)])

end
