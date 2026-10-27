module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Lists
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NodeFam

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section SmallCheck

variable (s : N6) (wTab uTab : List (List N6))

@[expose] def XLG (i j : ℕ) : List ℤ :=
  (wTab.getD i []).foldr refEL ((uTab.getD j []).foldr refEL (List.ofFn (omegaF s)))

@[expose] def BLG (i : ℕ) : List ℤ :=
  (wTab.getD i []).foldr refEL (List.ofFn (alphaF s))

@[expose] def resL (M a b : ℕ) (X B : List ℤ) : List ℤ :=
  List.zipWith (fun x β => ((a : ℤ) * x - 2 ^ b * β) % (M : ℤ)) X B

@[expose] def classCodes (A B M a b : ℕ) : List ℕ :=
  (List.range (A * B)).map fun m =>
    codeL (resL M a b (XLG s wTab uTab (m / B) (m % B)) (BLG s wTab (m / B)))

@[expose] def smallCheck (A B : ℕ) : Bool :=
  (List.range 6).all fun n => decide (n < 3) ||
    (List.range (2 ^ n - 1)).all fun a => decide (a = 0) ||
      (List.range n).all fun b => !(a.testBit b && a != 2 ^ b) ||
        strictB (msortR 12 (classCodes s wTab uTab A B (2 ^ n - 1) a b))

@[expose] def ClassSepSmall (A B : ℕ) : Prop :=
  ∀ n a b : ℕ, 3 ≤ n → n ≤ 5 → 0 < a → a < 2 ^ n - 1 → b < n → a.testBit b = true → a ≠ 2 ^ b →
    ∀ p q : Fin A × Fin B,
      (∀ i : N6, (((2 ^ n - 1 : ℕ) : ℤ)) ∣
        (((a : ℤ) • famX s (fun i : Fin A => wTab.getD i []) (fun j : Fin B => uTab.getD j [])
            p.1 p.2 - (2 : ℤ) ^ b • famB s (fun i : Fin A => wTab.getD i []) p.1) i -
         ((a : ℤ) • famX s (fun i : Fin A => wTab.getD i []) (fun j : Fin B => uTab.getD j [])
            q.1 q.2 - (2 : ℤ) ^ b • famB s (fun i : Fin A => wTab.getD i []) q.1) i)) → p = q

theorem resL_eq {A B : ℕ} (M a b : ℕ) (p : Fin A × Fin B) :
    resL M a b (XLG s wTab uTab p.1 p.2) (BLG s wTab p.1) =
      List.ofFn (fun i : N6 => (((a : ℤ) •
        famX s (fun i : Fin A => wTab.getD i []) (fun j : Fin B => uTab.getD j []) p.1 p.2 -
        (2 : ℤ) ^ b • famB s (fun i : Fin A => wTab.getD i []) p.1) i) % (M : ℤ)) := by
  have hX : XLG s wTab uTab p.1 p.2 =
      List.ofFn (famX s (fun i : Fin A => wTab.getD i []) (fun j : Fin B => uTab.getD j [])
        p.1 p.2) := by
    unfold XLG famX famY
    rw [ofFn_foldr_refEL, ofFn_foldr_refEL]
  have hB : BLG s wTab p.1 =
      List.ofFn (famB s (fun i : Fin A => wTab.getD i []) p.1) := by
    unfold BLG famB
    rw [ofFn_foldr_refEL]
  rw [hX, hB]
  unfold resL
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  simp

theorem smallCheck_sound {A B : ℕ} (h : smallCheck s wTab uTab A B = true) :
    ClassSepSmall s wTab uTab A B := by
  intro n a b hn3 hn5 ha0 haM hbn hbit hne p q hcong
  have hn : n ∈ List.range 6 := List.mem_range.2 (by omega)
  have h1 := (List.all_eq_true.1 h) n hn
  have h2 : (decide (n < 3) || (List.range (2 ^ n - 1)).all fun a => decide (a = 0) ||
      (List.range n).all fun b => !(a.testBit b && a != 2 ^ b) ||
        strictB (msortR 12 (classCodes s wTab uTab A B (2 ^ n - 1) a b))) = true := h1
  have h3 : decide (n < 3) = false := by simp; omega
  rw [h3, Bool.false_or] at h2
  have h4 := (List.all_eq_true.1 h2) a (List.mem_range.2 haM)
  have h5 : decide (a = 0) = false := by simp; omega
  rw [h5, Bool.false_or] at h4
  have h6 := (List.all_eq_true.1 h4) b (List.mem_range.2 hbn)
  have h7 : (!(a.testBit b && a != 2 ^ b)) = false := by simp [hbit, hne]
  rw [h7, Bool.false_or] at h6
  have hnd := nodup_of_strictB_R h6
  unfold classCodes at hnd
  rw [List.nodup_map_iff_inj_on List.nodup_range] at hnd
  have hmp : p.1.val * B + p.2.val < A * B := by
    have := p.1.isLt; have := p.2.isLt
    calc p.1.val * B + p.2.val < p.1.val * B + B := by omega
      _ = (p.1.val + 1) * B := by ring
      _ ≤ A * B := Nat.mul_le_mul_right _ (by omega)
  have hmq : q.1.val * B + q.2.val < A * B := by
    have := q.1.isLt; have := q.2.isLt
    calc q.1.val * B + q.2.val < q.1.val * B + B := by omega
      _ = (q.1.val + 1) * B := by ring
      _ ≤ A * B := Nat.mul_le_mul_right _ (by omega)
  have hBpos : 0 < B := lt_of_le_of_lt (Nat.zero_le _) p.2.isLt
  have hdiv : ∀ r : Fin A × Fin B, (r.1.val * B + r.2.val) / B = r.1.val ∧
      (r.1.val * B + r.2.val) % B = r.2.val := by
    intro r
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBpos, Nat.div_eq_of_lt r.2.isLt, zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.2.isLt]
  have hres : resL (2 ^ n - 1) a b (XLG s wTab uTab p.1 p.2) (BLG s wTab p.1) =
      resL (2 ^ n - 1) a b (XLG s wTab uTab q.1 q.2) (BLG s wTab q.1) := by
    rw [resL_eq, resL_eq]
    refine congrArg List.ofFn (funext fun i => ?_)
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd (hcong i))
  have := hnd (p.1.val * B + p.2.val) (List.mem_range.2 hmp) (q.1.val * B + q.2.val)
    (List.mem_range.2 hmq) (by
      simp only [(hdiv p).1, (hdiv p).2, (hdiv q).1, (hdiv q).2]
      rw [hres])
  have hpq1 : p.1.val = q.1.val := by
    have := congrArg (· / B) this
    simpa [(hdiv p).1, (hdiv q).1] using this
  have hpq2 : p.2.val = q.2.val := by
    have := congrArg (· % B) this
    simpa [(hdiv p).2, (hdiv q).2] using this
  exact Prod.ext (Fin.ext hpq1) (Fin.ext hpq2)

end SmallCheck

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
