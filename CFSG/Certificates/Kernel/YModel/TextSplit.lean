module

public import Certificates.Data.Kernel.YModel.Text
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

public section

namespace CFSG.KC.YModel

open CFSG.KC

@[expose] noncomputable def ymStep (w lines sgn : Nat) (C : Nat → List Nat) (E : Nat → Nat) (c : Nat)
    (ih : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool :=
  fun L e t v ng cur j rest => strictB (decV c) (fun d =>
      bIf(Nat.blt d (nat_lit 10),
        strictB (Nat.add (Nat.mul v (nat_lit 10)) d) (fun v' =>
          strictB (Nat.succ t) (fun t' => ih L e t' v' ng cur j rest)),
      bIf(Nat.beq c (nat_lit 45),
        bAnd(Nat.ble sgn L, bAnd(Nat.beq t (nat_lit 0), bAnd(Nat.beq ng (nat_lit 0),
          ih L e t v (nat_lit 1) cur j rest))),
      bIf(Nat.beq c (nat_lit 32),
        tokEnd w lines C E false L e t (tokCode sgn L v ng) cur j rest
          (fun L' e' cur' j' rest' => ih L' e' (nat_lit 0) (nat_lit 0) (nat_lit 0) cur' j' rest'),
      bIf(Nat.beq c (nat_lit 10),
        tokEnd w lines C E true L e t (tokCode sgn L v ng) cur j rest
          (fun L' e' cur' j' rest' => ih L' e' (nat_lit 0) (nat_lit 0) (nat_lit 0) cur' j' rest'),
        false)))))

@[expose] noncomputable def decRunWith (w lines sgn : Nat) (C : Nat → List Nat) (E : Nat → Nat)
    (bs : List Nat) (K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool)
    K (fun c _ ih => ymStep w lines sgn C E c ih) bs

theorem decRunWith_cons (w lines sgn : Nat) (C : Nat → List Nat) (E : Nat → Nat) (a : Nat)
    (A : List Nat) (K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool) :
    decRunWith w lines sgn C E (a :: A) K = ymStep w lines sgn C E a (decRunWith w lines sgn C E A K) :=
  rfl

@[expose] noncomputable def ymBase (lines : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool :=
  fun L _ t _ ng _ _ _ => bAnd(Nat.beq L lines, bAnd(Nat.beq t (nat_lit 0), Nat.beq ng (nat_lit 0)))

theorem decRun_eq_with (w lines sgn : Nat) (C : Nat → List Nat) (E : Nat → Nat) (bs : List Nat)
    (L e t v ng cur j : Nat) (rest : List Nat) :
    decRun w lines sgn C E bs L e t v ng cur j rest =
      decRunWith w lines sgn C E bs (ymBase lines) L e t v ng cur j rest :=
  rfl

theorem decRunWith_append (w lines sgn : Nat) (C : Nat → List Nat) (E : Nat → Nat)
    (A B : List Nat) (K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool) :
    decRunWith w lines sgn C E (A ++ B) K = decRunWith w lines sgn C E A (decRunWith w lines sgn C E B K) := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [List.cons_append, decRunWith_cons, decRunWith_cons, ih]

theorem decChunk_append (len N : Nat) (t u : List Nat) :
    decChunk len N (t ++ u) = decChunk len N t ++ u := by
  induction len generalizing N with
  | zero => rfl
  | succ n ih =>
    show List.cons _ (decChunk n _ (t ++ u)) = List.cons _ (decChunk n _ t) ++ u
    rw [ih]; rfl

theorem bytesOf_append (P Q : List (Nat × Nat)) : bytesOf (P ++ Q) = bytesOf P ++ bytesOf Q := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    obtain ⟨N, len⟩ := p
    show decChunk len N (bytesOf (P ++ Q)) = decChunk len N (bytesOf P) ++ bytesOf Q
    rw [ih, decChunk_append]

theorem ym_step {w lines sgn : Nat} {C : Nat → List Nat} {E : Nat → Nat} {CH : List (Nat × Nat)}
    {c m c' L e t v ng cur j : Nat} {rest : List Nat} {L' e' t' v' ng' cur' j' : Nat} {rest' : List Nat}
    (hp : ∀ K, decRunWith w lines sgn C E (bytesOf (List.take m (List.drop c CH))) K L e t v ng cur j rest =
      K L' e' t' v' ng' cur' j' rest') (hc : c + m = c') (K) :
    decRunWith w lines sgn C E (bytesOf (List.drop c CH)) K L e t v ng cur j rest =
      decRunWith w lines sgn C E (bytesOf (List.drop c' CH)) K L' e' t' v' ng' cur' j' rest' := by
  rw [← List.take_append_drop m (List.drop c CH), bytesOf_append, decRunWith_append, hp,
    List.drop_drop, ← hc, Nat.add_comm]

theorem ym_ok {w lines sgn : Nat} {C : Nat → List Nat} {E : Nat → Nat} {CH : List (Nat × Nat)}
    (hw : bAnd(Nat.blt (nat_lit 0) w, Nat.ble w (nat_lit 32)) = true)
    (h : decRun w lines sgn C E (bytesOf (List.drop (nat_lit 0) CH)) (nat_lit 0) (nat_lit 0) (nat_lit 0)
      (nat_lit 0) (nat_lit 0) (Nat.shiftRight (lhead (List.drop (nat_lit 0) (C (nat_lit 0)))) (nat_lit 0))
      (nat_lit 0) (List.drop (nat_lit 1) (C (nat_lit 0))) = true) :
    decBind (bytesOf CH) w lines sgn C E = true := by
  have e1 : Nat.shiftRight (lhead (List.drop (nat_lit 0) (C (nat_lit 0)))) (nat_lit 0) = lhead (C 0) := by
    rw [List.drop_zero]; rfl
  have e2 : List.drop (nat_lit 1) (C (nat_lit 0)) = ltail (C 0) := by
    cases C 0 <;> rfl
  rw [e1, e2, List.drop_zero] at h
  unfold decBind
  revert hw h
  cases Nat.blt (nat_lit 0) w <;> cases Nat.ble w (nat_lit 32) <;> simp

end CFSG.KC.YModel

end

open Lean Elab Tactic Meta in
elab "ymKernelRfl" : tactic => liftMetaFinishingTactic fun g => do
  let some (_, _, rhs) := (← whnfR (← g.getType)).eq? | throwError "ymKernelRfl: not an equation"
  g.assign (← mkEqRefl rhs)

elab "ymQuickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g => g.assign Lean.reflBoolTrue


open Lean Elab Command

namespace CFSG.KC.YModel.GenP

meta def natE : Expr := mkConst ``Nat
meta def listNatE : Expr := mkApp (mkConst ``List [0]) natE

meta def mkNatList (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) natE e acc) (mkApp (mkConst ``List.nil [0]) natE)

meta def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

meta def addTrueThm (name : Name) (b : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| (mkTheoremValEx name []
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)) reflBoolTrue [])

meta def withSync (x : CoreM Unit) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) x

meta def pairT : Expr := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)

meta def chunksE (b : ByteArray) (cb : Nat) : Expr := Id.run do
  let nch := (b.size + cb - 1) / cb
  let mut acc : Expr := mkApp (mkConst ``List.nil [0]) pairT
  for k' in [0:nch] do
    let k := nch - 1 - k'
    let s := k * cb
    let e := min b.size (s + cb)
    let mut v : Nat := 0
    for i in [0:e - s] do
      v := v + ((b.get! (s + i)).toNat <<< (8 * i))
    let p := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit v)
      (mkRawNatLit (e - s))
    acc := mkApp3 (mkConst ``List.cons [0]) pairT p acc
  return acc

meta def packLines (s : String) (w sgn : Nat) : Array Nat × Array Nat := Id.run do
  let ls := ((s.splitOn "\n").filter (· ≠ "")).toArray
  let mut F : Array Nat := #[]
  let mut E : Array Nat := #[]
  for L in [0:ls.size] do
    let toks := (ls[L]!).splitOn " "
    let mut acc := 0
    let mut e := 0
    for t in toks do
      let neg := t.startsWith "-"
      let v := (if neg then t.drop 1 else t).toString.toNat!
      let x := if L < sgn then v else 2 * v + (if neg then 1 else 0)
      acc := acc ||| (x <<< (w * e))
      e := e + 1
    F := F.push acc
    E := E.push e
  return (F, E)


elab "#ym_text_parts " pre:ident sId:ident path:str size:num hash:num wN:num sgnN:num cbN:(num)? :
    command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let b ← IO.FS.readBinFile path.getString
  unless b.size == size.getNat && b.hash.toNat == hash.getNat do
    throwError s!"{path.getString}: size {b.size} hash {b.hash.toNat}"
  let s := String.fromUTF8! b
  let w := wN.getNat
  let (F, E) := packLines s w (if sgnN.getNat == 0 then 1000000000 else sgnN.getNat)
  let sgn := if sgnN.getNat == 0 then F.size else sgnN.getNat
  let strE := mkConst ``String
  let chunksOf (x n : Nat) : Array Nat := Id.run do
    let mut out : Array Nat := #[]
    let mut y := x
    for _ in [0:(n + 31) / 32] do
      out := out.push (y % (2 ^ (32 * w)))
      y := y / (2 ^ (32 * w))
    return out
  let listListE : Expr := mkApp (mkConst ``List [0]) listNatE
  let clE : Expr := (F.zip E).foldr (fun (x, n) acc => mkApp3 (mkConst ``List.cons [0]) listNatE
    (mkNatList ((chunksOf x n).map mkRawNatLit)) acc) (mkApp (mkConst ``List.nil [0]) listNatE)
  withSync do
    addDef (P ++ `CH) (mkApp (mkConst ``List [0]) pairT) (chunksE b ((cbN.map (·.getNat)).getD 256))
    addDef (P ++ `Cl) listListE clE
    addDef (P ++ `El) listNatE (mkNatList (E.map mkRawNatLit))
    addDef (P ++ `F) (mkForall `L .default natE natE) (mkLambda `L .default natE
      (mkApp2 (mkConst ``CFSG.KC.YModel.joinW) (mkRawNatLit w)
        (mkApp2 (mkConst ``CFSG.KC.YModel.lgetL) (mkConst (P ++ `Cl)) (mkBVar 0))))
    addDef (P ++ `lines) natE (mkRawNatLit F.size)
    let rhs := mkApp (mkConst ``String.ofList) (mkApp (mkConst ``CFSG.KC.YModel.charsOf) (mkConst (P ++ `CH)))
    let nEq : Name := P ++ Name.mkSimple "eq"
    let tyEq := mkApp3 (mkConst ``Eq [1]) strE (mkConst sN) rhs
    let pfEq := mkApp2 (mkConst ``Eq.refl [1]) strE (mkConst sN)
    withOptions (maxRecDepth.set · 400000) do
      CFSG.KC.addThmDecl <| (mkTheoremValEx nEq [] tyEq pfEq [])

end CFSG.KC.YModel.GenP
