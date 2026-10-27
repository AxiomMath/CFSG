module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtRowsDef

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtF

open PkG Chain TtK

@[expose] noncomputable def forceN (y : ℕ) (k : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def forceB (y : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

theorem forceN_eq (y : ℕ) (k : ℕ → ℕ) : forceN y k = k y := by
  cases y <;> rfl

theorem forceB_eq (y : ℕ) (k : ℕ → Bool) : forceB y k = k y := by
  cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

@[expose] noncomputable def dgF (p i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight p (Nat.mul (nat_lit 6) i)) (nat_lit 63)

@[expose] noncomputable def compAuxF (t u n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.shiftLeft (dgF t (dgF u i)) (Nat.mul (nat_lit 6) i))) n

@[expose] noncomputable def compS (t u : ℕ) : ℕ :=
  forceN t (fun t => forceN u (fun u => compAuxF t u (nat_lit 48)))

theorem dgF_eq (p i : ℕ) : dgF p i = dg 64 p i := by
  have h63 : (63 : ℕ) = 2 ^ 6 - 1 := rfl
  change (p >>> (6 * i)) &&& 63 = p / 64 ^ i % 64
  rw [Nat.shiftRight_eq_div_pow, h63, Nat.and_two_pow_sub_one_eq_mod, pow_mul]
  norm_num

theorem compAuxF_eq (t u : ℕ) : ∀ n, compAuxF t u n = compAux 64 t u n
  | 0 => rfl
  | n + 1 => by
    change compAuxF t u n + (dgF t (dgF u n)) <<< (6 * n) = compAux 64 t u (n + 1)
    rw [compAuxF_eq t u n, dgF_eq, dgF_eq, Nat.shiftLeft_eq, pow_mul]
    simp only [compAux]
    norm_num

theorem compS_eq (t u : ℕ) : compS t u = comp 64 48 t u := by
  rw [compS, forceN_eq, forceN_eq]
  exact compAuxF_eq t u 48

@[expose] def one48 : ℕ :=
  370893620502133650990156577101181578910897003366124777934939121089380728434643182559296

theorem one_eq : one 64 48 = one48 := by decide +kernel

@[expose] noncomputable def evalWF (w : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) one48 (fun l _ ih => compS (base48.getD l one48) ih) w

theorem evalWF_cons (l : ℕ) (w : List ℕ) :
    evalWF (l :: w) = compS (base48.getD l one48) (evalWF w) := rfl

theorem evalWF_eq : ∀ w, evalWF w = evalW 64 48 base48 w
  | [] => by
    simp only [evalW, one_eq]
    rfl
  | l :: w => by
    rw [evalWF_cons, compS_eq, evalWF_eq w, ← one_eq]
    simp only [evalW]

@[expose] noncomputable def commPF (x a : ℕ) : Bool := compS x a == compS a x

@[expose] noncomputable def ccOkF (cc x : ℕ) : Bool :=
  let i := SP48.getD 1 one48
  let j := SP48.getD 3 one48
  let i' := SP48.getD 5 one48
  let j' := SP48.getD 7 one48
  (cc == 0 && !commPF x i) || (cc == 1 && commPF x i && !commPF x j) ||
    (cc == 2 && commPF x i && commPF x j && !commPF x i') ||
    (cc == 3 && commPF x i && commPF x j && commPF x i' && !commPF x j') ||
    (cc == 4 && commPF x i && commPF x j && commPF x i' && commPF x j')

@[expose] noncomputable def rowOkX (r : List ℕ) (x : ℕ) : Bool :=
  let gx := evalWF (rowG r)
  let gi := evalWF (invW6 (rowG r))
  (rowG r ++ rowW r).all (fun l => decide (l < 6)) &&
    ((compS x x == tP) == (r.getD 0 0 == 1)) && ccOkF (r.getD 1 0) x &&
    compS gx (compS x gi) == repP.getD (r.getD 2 0) one48

theorem rowVal_eq (r : List ℕ) : evalWF (rowW r) = rowVal r := by
  rw [evalWF_eq]
  rfl

theorem rowOk_eq (r : List ℕ) : rowOk r = rowOkX r (rowVal r) := by
  simp only [rowOk, rowOkX, ccOk, ccOkF, commP, commPF, compS_eq, evalWF_eq, one_eq]

@[expose] noncomputable def chainF (rows : List (List ℕ)) : ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → ℕ → Bool) (fun prev fin => Nat.beq prev fin)
    (fun a _ ih prev fin => forceB (evalWF (rowW a)) (fun v =>
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (ih v fin) (rowOkX a v)) (Nat.blt prev v))) rows

theorem chainF_cons (a : List ℕ) (rs : List (List ℕ)) (prev fin : ℕ) :
    chainF (a :: rs) prev fin = forceB (evalWF (rowW a)) (fun v =>
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (chainF rs v fin) (rowOkX a v))
        (Nat.blt prev v)) := rfl

theorem chainTo_eq_chainF : ∀ (rows : List (List ℕ)) (prev fin : ℕ),
    chainTo rowVal rowOk prev fin rows = chainF rows prev fin
  | [], prev, fin => by
    refine Bool.eq_iff_iff.2 ?_
    simp only [chainTo, chainF, beq_iff_eq, Nat.beq_eq]
  | a :: rs, prev, fin => by
    rw [chainF_cons, forceB_eq]
    simp only [bAnd_eq]
    rw [rowVal_eq, ← chainTo_eq_chainF rs, ← rowOk_eq]
    have hb : Nat.blt prev (rowVal a) = decide (prev < rowVal a) := by
      refine Bool.eq_iff_iff.2 ?_
      simp only [Nat.blt_eq, decide_eq_true_eq]
    rw [hb, ← Bool.and_assoc]
    rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtF

end
