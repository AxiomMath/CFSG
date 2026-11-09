module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
meta import all Lean.Shell
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KC.StrChunks

@[expose] noncomputable def pfxB : List Char → List Char → Bool := fun c =>
  List.rec (motive := fun _ => List Char → Bool) (fun _ => true)
    (fun a _ ih t => List.rec (motive := fun _ => Bool) false
      (fun b t' _ => Bool.rec (motive := fun _ => Bool) false (ih t') (Nat.beq a.toNat b.toNat)) t) c

@[expose] noncomputable def dropBy : List Char → List Char → List Char := fun c =>
  List.rec (motive := fun _ => List Char → List Char) (fun t => t)
    (fun _ _ ih t => List.rec (motive := fun _ => List Char) List.nil (fun _ t' _ => ih t') t) c

theorem char_eq_of_toNat {a b : Char} (h : a.toNat = b.toNat) : a = b :=
  Char.ext (UInt32.toNat_inj.mp h)

theorem pfxB_append : ∀ (c t : List Char), pfxB c t = true → c ++ dropBy c t = t
  | [], _, _ => rfl
  | _ :: _, [], h => Bool.noConfusion h
  | a :: c, b :: t, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (pfxB c t) (Nat.beq a.toNat b.toNat) = true := h
    cases hb : Nat.beq a.toNat b.toNat
    · rw [hb] at h'
      exact Bool.noConfusion h'
    · rw [hb] at h'
      have e := char_eq_of_toNat (Nat.eq_of_beq_eq_true hb)
      subst e
      show a :: (c ++ dropBy c t) = a :: t
      rw [pfxB_append c t h']

end CFSG.KC.StrChunks

end

namespace CFSG.KC.StrChunksSfx

meta def addDeclDeep (mb : Nat) (x : CoreM Unit) : CoreM Unit := do
  let ctx ← read
  let s ← get
  Lean.Internal.setThreadStackSize (USize.ofNat (mb * 1024 * 1024))
  let t ← IO.asTask (prio := .dedicated) (x.toIO ctx s)
  let r ← IO.wait t
  Lean.Internal.setThreadStackSize (USize.ofNat (8 * 1024 * 1024))
  match r with
  | .ok ((), s') => set s'
  | .error e => throwError m!"{e}"

end CFSG.KC.StrChunksSfx

open CFSG.KC.Tab CFSG.KC.StrChunks CFSG.KC.StrChunksSfx in
elab "#str_chunks_sfx " pre:ident sId:ident kN:num depth:num stackMB:num : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← match ((← getEnv).find? sN).bind ConstantInfo.value? with
    | some (.lit (.strVal s)) => pure s
    | _ => throwError "#str_chunks_sfx: {sN} is not a string literal"
  let k := kN.getNat
  if k == 0 then throwError "#str_chunks_sfx: the chunk size is 0"
  let cs := s.toList.toArray
  let n := max 1 ((cs.size + k - 1) / k)
  let charE : Expr := mkConst ``Char
  let lty := mkApp (mkConst ``List [0]) charE
  let consC := mkApp (mkConst ``List.cons [0]) charE
  let nilC := mkApp (mkConst ``List.nil [0]) charE
  let app ← liftTermElabM do
    let e ← Term.elabTerm (← `(fun (a b : List Char) => a ++ b)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let mut chE : Std.HashMap Nat Expr := {}
  for c in cs do
    unless chE.contains c.toNat do
      chE := chE.insert c.toNat (mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat))
  let cN := fun (j : Nat) => P ++ Name.mkSimple s!"c{j}"
  let sfN := fun (j : Nat) => P ++ Name.mkSimple s!"sfx{j}"
  let pfN := fun (j : Nat) => P ++ Name.mkSimple s!"pfx{j}"
  let drN := fun (j : Nat) => P ++ Name.mkSimple s!"drp{j}"
  let caN := fun (j : Nat) => P ++ Name.mkSimple s!"cat{j}"
  let strE := mkConst ``String
  let boolE := mkConst ``Bool
  let eqE := fun (ty a b : Expr) => mkApp3 (mkConst ``Eq [1]) ty a b
  let reflE := fun (ty a : Expr) => mkApp2 (mkConst ``Eq.refl [1]) ty a
  let symmE := fun (ty a b h : Expr) => mkApp4 (mkConst ``Eq.symm [1]) ty a b h
  let transE := fun (ty a b c h1 h2 : Expr) => mkAppN (mkConst ``Eq.trans [1]) #[ty, a, b, c, h1, h2]
  let congrE := fun (α β a b f h : Expr) => mkAppN (mkConst ``congrArg [1, 1]) #[α, β, a, b, f, h]
  let catE := fun (j : Nat) (x : Expr) => (mkApp2 app (mkConst (cN j)) x).headBeta
  let catF := fun (j : Nat) => mkLambda `x .default lty (catE j (.bvar 0))
  let thmV := fun (name : Name) (type value : Expr) =>
    CFSG.KC.addThmDecl ({ name := name, levelParams := [], type := type, value := value } : TheoremVal)
  let deep := fun (x : CoreM Unit) =>
    addDeclDeep stackMB.getNat <| withOptions (maxRecDepth.set · depth.getNat) x
  withSync do
    for j in [0:n] do
      let lo := j * k
      let hi := min cs.size (lo + k)
      let mut acc := nilC
      for i' in [0:hi - lo] do
        acc := mkApp2 consC chE[cs[hi - 1 - i']!.toNat]! acc
      addDef (cN j) lty acc
    addDef (P ++ `n) natT (lit n)
    let mut t := mkConst (cN (n - 1))
    let mut rs : Array Expr := #[t]
    for j' in [1:n] do
      t := (mkApp2 app (mkConst (cN (n - 1 - j'))) t).headBeta
      rs := rs.push t
    rs := rs.reverse
    addDef (P ++ `chars) lty t
    let mut acc := nilC
    let mut sfx : Array Expr := Array.replicate n nilC
    for i' in [0:cs.size] do
      let i := cs.size - 1 - i'
      acc := mkApp2 consC chE[cs[i]!.toNat]! acc
      if i % k == 0 then sfx := sfx.set! (i / k) acc
    for j in [0:n] do
      deep <| addDef (sfN j) lty sfx[j]!
    for j in [0:n - 1] do
      let cj := mkConst (cN j)
      let sj := mkConst (sfN j)
      let sj1 := mkConst (sfN (j + 1))
      deep <| thmV (pfN j) (eqE boolE (mkApp2 (mkConst ``pfxB) cj sj) (mkConst ``Bool.true))
        (reflE boolE (mkConst ``Bool.true))
      let dr := mkApp2 (mkConst ``dropBy) cj sj
      deep <| thmV (drN j) (eqE lty dr sj1) (reflE lty sj1)
      let h1 := symmE lty (catE j dr) (catE j sj1) (congrE lty lty dr sj1 (catF j) (mkConst (drN j)))
      let h2 := mkApp3 (mkConst ``pfxB_append) cj sj (mkConst (pfN j))
      thmV (caN j) (eqE lty (catE j sj1) sj) (transE lty (catE j sj1) (catE j dr) sj h1 h2)
    let mut e := reflE lty (mkConst (cN (n - 1)))
    for j' in [1:n] do
      let j := n - 1 - j'
      let h1 := congrE lty lty rs[j + 1]! (mkConst (sfN (j + 1))) (catF j) e
      e := transE lty rs[j]! (catE j (mkConst (sfN (j + 1)))) (mkConst (sfN j)) h1 (mkConst (caN j))
    deep <| thmV (P ++ `chars_sfx) (eqE lty (mkConst (P ++ `chars)) (mkConst (sfN 0))) e
    let ofL := fun x => mkApp (mkConst ``String.ofList) x
    deep <| thmV (P ++ `eq0) (eqE strE (mkConst sN) (ofL (mkConst (sfN 0)))) (reflE strE (mkConst sN))
    let h := congrE lty strE (mkConst (sfN 0)) (mkConst (P ++ `chars)) (mkConst ``String.ofList)
      (symmE lty (mkConst (P ++ `chars)) (mkConst (sfN 0)) (mkConst (P ++ `chars_sfx)))
    thmV (P ++ `eq) (eqE strE (mkConst sN) (ofL (mkConst (P ++ `chars))))
      (transE strE (mkConst sN) (ofL (mkConst (sfN 0))) (ofL (mkConst (P ++ `chars)))
        (mkConst (P ++ `eq0)) h)
