module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Mask

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu Certificates.RouteP.M24Defect

theorem bp_eq_sum (m w : ℕ) :
    bp m w = ∑ c ∈ Finset.range 11,
      (if m.testBit c then (1 : ZMod 2) else 0) * (if w.testBit c then (1 : ZMod 2) else 0) := by
  simp only [bp, dotProduct]
  rw [← Fin.sum_univ_eq_sum_range (fun c : ℕ =>
    (if m.testBit c then (1 : ZMod 2) else 0) *
      (if w.testBit c then (1 : ZMod 2) else 0))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [bvec_apply]

private theorem natCast_zmod_two_eq_ite (n : ℕ) :
    (n : ZMod 2) = if n % 2 = 1 then (1 : ZMod 2) else 0 := by
  conv_lhs => rw [← ZMod.natCast_mod n 2]
  split_ifs with h
  · rw [h]; norm_num
  · have h0 : n % 2 = 0 := by
      have := Nat.mod_lt n (by norm_num : 0 < 2)
      omega
    rw [h0]; norm_num

private theorem ite_testBit_zero_eq_cast (n : ℕ) :
    (if n.testBit 0 then (1 : ZMod 2) else 0) = (n : ZMod 2) := by
  simp only [Nat.testBit_zero, decide_eq_true_eq]
  exact (natCast_zmod_two_eq_ite n).symm

private theorem bp_ite_zero (m : ℕ) (p : Prop) [Decidable p] (c : ℕ) :
    bp m (if p then c else 0) = if p then bp m c else 0 := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, bp_zero_right]

private theorem mul_ite_one (a : ZMod 2) (p : Prop) [Decidable p] :
    a * (if p then (1 : ZMod 2) else 0) = if p then a else 0 := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp, mul_one]
  · rw [if_neg hp, if_neg hp, mul_zero]

private theorem testBit_dualAct_zero (c : ℕ) (cs : List ℕ) (m : ℕ) :
    (dualAct (c :: cs) m).testBit 0 = decide (popc 11 (m &&& c) % 2 = 1) := by
  have hlt : popc 11 (m &&& c) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [dualAct, Nat.testBit_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem testBit_dualAct_succ (c : ℕ) (cs : List ℕ) (m j : ℕ) :
    (dualAct (c :: cs) m).testBit (j + 1) = (dualAct cs m).testBit j := by
  have hlt : popc 11 (m &&& c) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [dualAct, Nat.testBit_succ, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

private theorem bp_dualAct_aux : ∀ (cols : List ℕ) (m w : ℕ),
    (∑ j ∈ Finset.range cols.length,
        (if (dualAct cols m).testBit j then (1 : ZMod 2) else 0) *
          (if w.testBit j then (1 : ZMod 2) else 0)) = bp m (actM cols w)
  | [], m, w => by simp [actM, bp_zero_right]
  | c :: cs, m, w => by
    have htail : (∑ j ∈ Finset.range cs.length,
        (if (dualAct (c :: cs) m).testBit (j + 1) then (1 : ZMod 2) else 0) *
          (if w.testBit (j + 1) then (1 : ZMod 2) else 0))
        = bp m (actM cs (w / 2)) := by
      have h : ∀ j, (if (dualAct (c :: cs) m).testBit (j + 1) then (1 : ZMod 2) else 0) *
          (if w.testBit (j + 1) then (1 : ZMod 2) else 0)
          = (if (dualAct cs m).testBit j then (1 : ZMod 2) else 0) *
            (if (w / 2).testBit j then (1 : ZMod 2) else 0) := by
        intro j
        rw [testBit_dualAct_succ c cs m j, Nat.testBit_succ]
      rw [Finset.sum_congr rfl (fun j _ => h j)]
      exact bp_dualAct_aux cs m (w / 2)
    have hhead : (if (dualAct (c :: cs) m).testBit 0 then (1 : ZMod 2) else 0)
        = (popc 11 (m &&& c) : ZMod 2) := by
      rw [testBit_dualAct_zero c cs m]
      simp only [decide_eq_true_eq]
      exact (natCast_zmod_two_eq_ite _).symm
    have hw0 : (if w.testBit 0 then (1 : ZMod 2) else 0)
        = (if w % 2 = 1 then (1 : ZMod 2) else 0) := by
      simp only [Nat.testBit_zero, decide_eq_true_eq]
    have hbpc : bp m c = (popc 11 (m &&& c) : ZMod 2) := by
      rw [bp]; exact bvec_dotProduct 11 m c
    rw [List.length_cons, Finset.sum_range_succ', htail, hhead, hw0, actM, bp_xor_right,
      bp_ite_zero, hbpc, mul_ite_one]
    exact add_comm _ _

theorem bp_dualAct {cols : List ℕ} (h : cols.length = 11) (m w : ℕ) :
    bp (dualAct cols m) w = bp m (actM cols w) := by
  rw [bp_eq_sum]
  rw [← h]
  exact bp_dualAct_aux cols m w

theorem sum_bp_regroup {α : Type*} (L : List α) (key val : α → ℕ) (f : ℕ → ℕ) (N : ℕ)
    (hk : ∀ x ∈ L, key x < N) :
    (L.map fun x => bp (val x) (f (key x))).sum =
      ∑ κ ∈ Finset.range N, bp (xorMasks ((L.filter fun x => key x == κ).map val)) (f κ) := by
  induction L with
  | nil => simp [xorMasks, bp_zero_left]
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons,
      ih (fun y hy => hk y (List.mem_cons_of_mem x hy))]
    have hterm : ∀ κ : ℕ,
        bp (xorMasks (((x :: L).filter fun y => key y == κ).map val)) (f κ)
          = bp (xorMasks ((L.filter fun y => key y == κ).map val)) (f κ)
            + (if key x = κ then bp (val x) (f κ) else 0) := by
      intro κ
      by_cases h : key x = κ
      · have hb : (key x == κ) = true := by simpa [beq_iff_eq] using h
        rw [List.filter_cons, if_pos hb, if_pos h, List.map_cons, xorMasks, bp_xor_left]
        exact add_comm _ _
      · have hb : ¬ ((key x == κ) = true) := by
          simp only [beq_iff_eq]; exact h
        rw [List.filter_cons, if_neg hb, if_neg h, add_zero]
    rw [Finset.sum_congr rfl (fun κ _ => hterm κ), Finset.sum_add_distrib,
      Finset.sum_ite_eq_of_mem _ _ _
        (Finset.mem_range.mpr (hk x List.mem_cons_self))]
    exact add_comm _ _

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n m : ℕ) :
    ∑ κ ∈ Finset.range (n * m), f κ =
      ∑ i ∈ Finset.range n, ∑ c ∈ Finset.range m, f (m * i + c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.mul_comm n m]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
