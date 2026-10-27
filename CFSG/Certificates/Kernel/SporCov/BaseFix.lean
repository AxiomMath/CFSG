module

public import Certificates.Data.Kernel.SporCov.BaseFix
public import CFSG.Certificates.Kernel.SporCov.BaseKit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.KC.Loop CFSG.Sporadic.Th

theorem natRec_add_sumF (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
      ∑ l ∈ Finset.range k, F l
  | 0 => by simp
  | k + 1 => by
    change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
    rw [natRec_add_sumF F k, Finset.sum_range_succ, Nat.add_comm]

theorem sumBelow_sumF (m : ℕ) (f : ℕ → ℕ) : ∀ hi, sumBelow m hi f =
    ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m)
  | 0 => by simp [sumBelow]
  | hi + 1 => by
    have e : sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64) (sumBelow m hi f) := rfl
    have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
      change hi <<< 6 + l = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e, natRec_add_sumF, sumBelow_sumF m f hi, Nat.mul_succ, Finset.sum_range_add]
    simp only [e2]
    exact Nat.add_comm _ _

theorem sumBelow_specF {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  rw [sumBelow_sumF]
  obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
  rw [hd, Finset.sum_range_add]
  have h2 : ∑ l ∈ Finset.range d,
      Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hb : Nat.blt (m + l) m = false := by
      cases e : Nat.blt (m + l) m
      · rfl
      · rw [Nat.blt_eq] at e
        omega
    rw [hb]
  rw [h2, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact Finset.mem_range.1 hi
  rw [hb]

theorem natRec_bAnd (F : ℕ → Bool) : ∀ k,
    Nat.rec (motive := fun _ => Bool) true
      (fun l ih => Bool.rec (motive := fun _ => Bool) false ih (F l)) k = true →
    ∀ l < k, F l = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | k + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun l ih => Bool.rec (motive := fun _ => Bool) false ih (F l)) k) (F k) = true at h
    cases hF : F k
    · rw [hF] at h
      exact absurd h Bool.false_ne_true
    · rw [hF] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact natRec_bAnd F k h l hl
      · exact hF

theorem allBelow_specF {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := natRec_bAnd (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2
        ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l))) 64) hi h (i / 64) (by omega)
  have h2 := natRec_bAnd (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem agB_spec {f g : ℕ → ℕ} {m hi : ℕ} (h : agB f g m hi = true) (hm : m ≤ 64 * hi) :
    ∀ x < m, f x = g x := fun x hx =>
  Nat.eq_of_beq_eq_true (allBelow_specF h hm x hx)

theorem invB_spec {f g : ℕ → ℕ} {m hi : ℕ} (h : invB f g m hi = true) (hm : m ≤ 64 * hi) :
    ∀ x < m, g (f x) = x := fun x hx =>
  Nat.eq_of_beq_eq_true (allBelow_specF h hm x hx)

variable {G : Type} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] noncomputable def fixN (g : G) : ℕ :=
  (Finset.univ.filter fun i : Fin n => g • i = i).card

theorem fixN_conj (g c : G) : fixN (n := n) (c * g * c⁻¹) = fixN (n := n) g := by
  unfold fixN
  refine Finset.card_bij (fun i _ => c⁻¹ • i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have e := congrArg (fun j => c⁻¹ • j) hi
    simp only [mul_smul, inv_smul_smul] at e
    exact e
  · intro i _ j _ hij
    exact smul_left_cancel _ hij
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨c • j, ?_, by rw [inv_smul_smul]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_smul, mul_smul, inv_smul_smul, hj]

theorem fixN_of_isConj {g h : G} (hc : IsConj g h) : fixN (n := n) g = fixN (n := n) h := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact (fixN_conj g c).symm

section Kit

variable {a b : G} {fA fAi fB fBi : ℕ → ℕ} (hA : ∀ x < n, fA x = idx n a x)
  (hAi : ∀ x < n, fAi x = idx n a⁻¹ x) (hB : ∀ x < n, fB x = idx n b x)
  (hBi : ∀ x < n, fBi x = idx n b⁻¹ x)
include hA hAi hB hBi

theorem fixB_eq {hi : ℕ} (hm : n ≤ 64 * hi) (w : List ℕ) :
    fixB fA fAi fB fBi n hi w = fixN (n := n) (wE (fP a b) w) := by
  unfold fixB fixN
  rw [sumBelow_specF _ hm, ← Fin.sum_univ_eq_sum_range, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [imB_eq hA hAi hB hBi w i.isLt, idx_of_lt _ i.isLt]
  by_cases h : wE (fP a b) w • i = i
  · rw [if_pos h, h, Nat.beq_refl]
  · rw [if_neg h]
    have hb : Nat.beq (wE (fP a b) w • i).val i.val = false := by
      cases e : Nat.beq (wE (fP a b) w • i).val i.val
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true e)) h
    rw [hb]

end Kit

end CFSG.KD.SporCov

end
