module

public import Certificates.Data.Kernel.OpsMcertN
public import CFSG.Certificates.Kernel.Common.SliceGlue
public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.Benes
meta import all CFSG.Certificates.Kernel.Common.Benes

set_option maxRecDepth 400000

public section

open Lean Elab Command Term in
meta def kcRegsMNCmd (id : Ident) (t : Term) (W N : Nat) : CommandElabM Unit := do
  let base := (← getCurrNamespace) ++ id.getId
  let v ← liftTermElabM do
    let e ← elabTerm t (some (Lean.mkConst ``Nat))
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar || e.hasFVar then throwError "#kc_regs_mn: the term is not closed"
    CFSG.KC.Benes.kNat (toString id.getId) e
  let mask := (1 <<< W) - 1
  let natE := Lean.mkConst ``Nat
  liftCoreM do
    for i in [0:N] do
      CFSG.KC.Load.addDef (base.appendAfter s!"_{i}") natE (mkRawNatLit ((v >>> (W * i)) &&& mask)) true
    let lst := (List.range N).foldr (fun i acc => mkApp3 (Lean.mkConst ``List.cons [0]) natE
      (Lean.mkConst (base.appendAfter s!"_{i}")) acc) (mkApp (Lean.mkConst ``List.nil [0]) natE)
    CFSG.KC.Load.addDef base (mkApp (Lean.mkConst ``List [0]) natE) lst true

elab "#kc_regs_mn " id:ident " := " t:term " width " w:num " count " n:num : command =>
  kcRegsMNCmd id t w.getNat n.getNat

namespace CFSG.KC.OpsMN

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK CFSG.KC

@[expose] noncomputable def packR (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor x (Nat.shiftLeft ih w)) l

@[expose] noncomputable def listEqN : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y r _ => bAnd(Nat.beq x y, ih r)) b)

theorem listEqN_spec : ∀ {a b : List Nat}, listEqN a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [listEqN])
  | _ :: _, [], h => absurd h (by simp [listEqN])
  | x :: a, y :: b, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (listEqN a b) (Nat.beq x y) = true := h
    cases hb : Nat.beq x y
    · rw [hb] at h'; exact absurd h' (by simp)
    · rw [hb] at h'
      rw [Nat.eq_of_beq_eq_true hb, listEqN_spec h']

variable {V : Type} (O : Ops Nat V)

@[expose] noncomputable def stepS (R : List Nat) (op : Op) : List Nat :=
  Op.rec (motive := fun _ => List Nat)
    (fun i j t => R.set t (O.mul (getN R i) (getN R j)))
    (fun e i t => R.set t (powN O (Nat.succ e) (getN R i) e)) op

@[expose] noncomputable def runS (prog : List Op) (R : List Nat) : List Nat := prog.foldl (stepS O) R

theorem forceB_eqS (y : Nat) (k : Nat → Bool) : forceB y k = k y := by cases y <;> rfl

theorem forceL_eqS : ∀ (xs : List Nat) (k : List Nat → Bool), forceL xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by
    show forceB x (fun x' => forceL xs fun l => k (x' :: l)) = k (x :: xs)
    rw [forceB_eqS, forceL_eqS]

theorem runN_eqS : ∀ (prog : List Op) (R : List Nat) (k : List Nat → Bool),
    runN O prog R k = k (runS O prog R)
  | [], _, _ => rfl
  | op :: prog, R, k => by
    show stepN O R (fun R' => runN O prog R' k) op = k (runS O prog (stepS O R op))
    cases op with
    | mul i j t =>
      show forceB _ (fun a => forceL _ _) = _
      rw [forceB_eqS, forceL_eqS, runN_eqS]; rfl
    | pow e i t =>
      show forceB _ (fun a => forceL _ _) = _
      rw [forceB_eqS, forceL_eqS, runN_eqS]; rfl

@[expose] noncomputable def segOK (seg : List Op) (S S' : List Nat) : Bool :=
  runN O seg S fun R => listEqN R S'

theorem runS_of_segOK {seg : List Op} {S S' : List Nat} (h : segOK O seg S S' = true) :
    runS O seg S = S' := by
  unfold segOK at h
  rw [runN_eqS] at h
  exact listEqN_spec h

theorem runS_of_cuts (prog : List Op) (cs : List Nat) (Sn : Nat → List Nat) (m : Nat)
    (h0 : cs.getD 0 0 = 0) (hend : prog.length ≤ cs.getD m 0)
    (hmono : ∀ j < m, cs.getD j 0 ≤ cs.getD (j + 1) 0)
    (h : ∀ j < m, segOK O (SliceGlue.slice prog (cs.getD j 0) (cs.getD (j + 1) 0 - cs.getD j 0))
      (Sn j) (Sn (j + 1)) = true) :
    runS O prog (Sn 0) = Sn m := by
  have key : ∀ j, j ≤ m → runS O (prog.take (cs.getD j 0)) (Sn 0) = Sn j := by
    intro j
    induction j with
    | zero => intro _; rw [h0]; rfl
    | succ j ih =>
      intro hj
      have e : cs.getD (j + 1) 0 = cs.getD j 0 + (cs.getD (j + 1) 0 - cs.getD j 0) := by
        have := hmono j (by omega); omega
      rw [e, List.take_add]
      unfold runS
      rw [List.foldl_append]
      have := ih (by omega)
      unfold runS at this
      rw [this]
      exact runS_of_segOK O (h j (by omega))
  have := key m (Nat.le_refl m)
  rwa [List.take_of_length_le hend] at this

theorem regsN_of_runS (A B n : Nat) (prog : List Op) (k : List Nat → Bool) (S0 Sm : List Nat)
    (h0 : listEqN (initN O A B n) S0 = true) (hrun : runS O prog S0 = Sm) (hk : k Sm = true) :
    regsN O A B n prog k = true := by
  unfold regsN
  rw [runN_eqS, listEqN_spec h0, hrun]
  exact hk

theorem regsN_of_runS_init (A B n : Nat) (prog : List Op) (k : List Nat → Bool) (Sm : List Nat)
    (hrun : runS O prog (initN O A B n) = Sm) (hk : k Sm = true) : regsN O A B n prog k = true := by
  unfold regsN
  rw [runN_eqS, hrun]
  exact hk

end CFSG.KC.OpsMN

end
