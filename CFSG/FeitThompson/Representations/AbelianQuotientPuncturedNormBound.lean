module

public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import Mathlib.Algebra.Order.Chebyshev
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem cfInner_self_sum_intCast_smul {G : Type*} [Group G] [Fintype G] {S : Finset (G → ℂ)}
    (hS : ↑S ⊆ Irr G) (b : (G → ℂ) → ℤ) :
    cfInner (∑ χ ∈ S, (b χ : ℂ) • χ) (∑ χ ∈ S, (b χ : ℂ) • χ)
      = ((∑ χ ∈ S, b χ ^ 2 : ℤ) : ℂ) := by
  classical
  rw [cfInner_sum_left]
  push_cast
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [cfInner_smul_left, cfInner_sum_right]
  have key : ∀ ψ ∈ S, cfInner (χ : G → ℂ) ((b ψ : ℂ) • ψ)
      = if χ = ψ then (b ψ : ℂ) else 0 := by
    intro ψ hψ
    rw [cfInner_smul_right, cfInner_eq_ite_of_mem_Irr (hS hχ) (hS hψ)]
    simp
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq _ _ (fun ψ => (b ψ : ℂ)), if_pos hχ]
  ring

theorem span_irrTrivialOn_le_virtualChars {G : Type*} [Group G] (P : Subgroup G) :
    Submodule.span ℤ (irrTrivialOn P) ≤ virtualChars G :=
  Submodule.span_le.2 fun _ hχ => Irr_subset_virtualChars (irrTrivialOn_subset_Irr hχ)

theorem mem_span_irrTrivialOn_of_cfInner_eq_zero {G : Type*} [Group G] [Fintype G]
    {P : Subgroup G} {α : G → ℂ} (hα : α ∈ Submodule.span ℤ (Irr G))
    (h : ∀ χ ∈ Irr G, χ ∉ irrTrivialOn P → cfInner α χ = 0) :
    α ∈ Submodule.span ℤ (irrTrivialOn P) := by
  classical
  have : Fintype (Irr G) := Fintype.ofFinite _
  obtain ⟨n, rfl⟩ := mem_span_Irr_iff_exists_intCast_sum.1 hα
  refine Submodule.sum_mem _ fun χ _ => ?_
  rcases eq_or_ne (n χ) 0 with h0 | h0
  · simp [h0]
  · have hmem : (χ : G → ℂ) ∈ irrTrivialOn P := by
      by_contra hc
      have hzero := h (χ : G → ℂ) χ.2 hc
      rw [cfInner_intCast_sum_Irr_coe n χ] at hzero
      exact h0 (by exact_mod_cast hzero)
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

private theorem int_abs_le_sq (z : ℤ) : |z| ≤ z ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · calc |z| = 1 * |z| := (one_mul _).symm
      _ ≤ |z| * |z| := mul_le_mul_of_nonneg_right (Int.one_le_abs hz) (abs_nonneg z)
      _ = z ^ 2 := by rw [← sq_abs]; ring

private theorem int_sub_one_le {h k n s : ℤ} (hh : 0 ≤ h) (hk : 2 * k ≤ h) (hn : 1 ≤ n)
    (hkn : s ^ 2 ≤ k * n) (hnn : s ^ 2 ≤ n ^ 2) : h - 1 ≤ h * n - s ^ 2 := by
  rcases eq_or_lt_of_le hn with rfl | hn2
  · nlinarith
  · have hhk : 0 ≤ h - k := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ n - 2) hhk]

theorem card_irrTrivialOnFinset_eq_index {H : Type*} [CommGroup H] [Finite H] {P : Subgroup H} :
    (irrTrivialOnFinset P).card = P.index := by
  have : Fintype H := Fintype.ofFinite H
  have h := sum_sq_degree_irrTrivialOn_eq_index (N := P) (G := H)
  rw [Finset.sum_congr rfl (fun χ hχ => by
    rw [Irr.apply_one_eq_one (irrTrivialOn_subset_Irr (mem_irrTrivialOnFinset.1 hχ)), one_pow])] at h
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact Nat.cast_injective (R := ℂ) h

variable {H : Type*} [CommGroup H] [Fintype H] {P : Subgroup H}

theorem sum_norm_sq_compl_one_ge_of_mem_span_irrTrivialOn [DecidableEq H] (hP : P ≠ ⊥)
    {α : H → ℂ} (hα : α ∈ Submodule.span ℤ (irrTrivialOn P)) (hα0 : α ≠ 0) :
    (Nat.card H : ℝ) - 1 ≤ ∑ x ∈ ({1} : Finset H)ᶜ, ‖α x‖ ^ 2 := by
  classical
  set S : Finset (H → ℂ) := irrTrivialOnFinset P with hSdef
  have hcoe : (irrTrivialOn P : Set (H → ℂ)) = ↑S := by ext χ; simp [hSdef]
  rw [hcoe] at hα
  obtain ⟨b, -, hb⟩ := Submodule.mem_span_finset.1 hα
  have hb' : α = ∑ χ ∈ S, ((b χ : ℂ)) • χ := by
    rw [← hb]
    exact Finset.sum_congr rfl fun χ _ => (Int.cast_smul_eq_zsmul ℂ (b χ) χ).symm
  have hSIrr : ↑S ⊆ Irr H := fun χ hχ =>
    irrTrivialOn_subset_Irr (mem_irrTrivialOnFinset.1 hχ)
  set N : ℤ := ∑ χ ∈ S, b χ ^ 2 with hNdef
  set s : ℤ := ∑ χ ∈ S, b χ with hsdef
  have hchar1 : ∀ χ ∈ S, χ (1 : H) = (1 : ℂ) := fun χ hχ => Irr.apply_one_eq_one (hSIrr hχ)
  have hcardZ : (S.card : ℤ) = (P.index : ℤ) := by
    rw [hSdef, card_irrTrivialOnFinset_eq_index]
  have hα1 : α (1 : H) = (s : ℂ) := by
    rw [hb', Finset.sum_apply]
    push_cast [hsdef]
    exact Finset.sum_congr rfl fun χ hχ => by simp [hchar1 χ hχ]
  have hinner : cfInner α α = (N : ℂ) := by
    rw [hb']; exact cfInner_self_sum_intCast_smul hSIrr b
  have h1 := cfInner_self_eq_sum_norm_sq α
  rw [hinner] at h1
  have hne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : ((Nat.card H : ℂ)) * (N : ℂ) = ∑ g : H, ((‖α g‖ : ℂ)) ^ 2 := by
    rw [h1]; field_simp
  have hsumR : ∑ g : H, ‖α g‖ ^ 2 = (Nat.card H : ℝ) * (N : ℝ) := by exact_mod_cast h2.symm
  have hNnonneg : 0 ≤ N := Finset.sum_nonneg fun χ _ => sq_nonneg (b χ)
  have hN1 : 1 ≤ N := by
    rcases hNnonneg.lt_or_eq with hlt | heq
    · omega
    · refine absurd ?_ hα0
      have hz : ∀ χ ∈ S, b χ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun χ _ => sq_nonneg (b χ)).1 heq.symm
      rw [hb']
      refine Finset.sum_eq_zero fun χ hχ => ?_
      have hbχ : b χ = 0 := pow_eq_zero_iff (by norm_num) |>.1 (hz χ hχ)
      simp [hbχ]
  have hsq_k : s ^ 2 ≤ (S.card : ℤ) * N := by
    rw [hsdef, hNdef]; exact sq_sum_le_card_mul_sum_sq
  have habs : |s| ≤ N :=
    calc |s| ≤ ∑ χ ∈ S, |b χ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ N := Finset.sum_le_sum fun χ _ => int_abs_le_sq (b χ)
  have hsq_N : s ^ 2 ≤ N ^ 2 := by
    obtain ⟨h₁, h₂⟩ := abs_le.1 habs
    exact sq_le_sq' h₁ h₂
  have hPcard : 2 ≤ Nat.card P := (Subgroup.one_lt_card_iff_ne_bot P).2 hP
  have h2k : 2 * P.index ≤ Nat.card H :=
    calc 2 * P.index = P.index * 2 := by ring
      _ ≤ P.index * Nat.card P := Nat.mul_le_mul_left _ hPcard
      _ = Nat.card H := Subgroup.index_mul_card P
  have key : (Nat.card H : ℤ) - 1 ≤ (Nat.card H : ℤ) * N - s ^ 2 :=
    int_sub_one_le (by positivity) (k := (P.index : ℤ)) (by exact_mod_cast h2k) hN1
      (by rw [← hcardZ]; exact hsq_k) hsq_N
  have hcompl : ∑ x ∈ ({1} : Finset H)ᶜ, ‖α x‖ ^ 2
      = (∑ x : H, ‖α x‖ ^ 2) - ‖α (1 : H)‖ ^ 2 := by
    rw [Finset.compl_singleton, Finset.sum_erase_eq_sub (Finset.mem_univ (1 : H))]
  have hone : ‖α (1 : H)‖ ^ 2 = ((s : ℝ)) ^ 2 := by rw [hα1, Complex.norm_intCast, sq_abs]
  rw [hcompl, hsumR, hone]
  exact_mod_cast key

theorem sum_norm_sq_compl_one_ge_of_cfInner_eq_zero [DecidableEq H] (hP : P ≠ ⊥) {α : H → ℂ}
    (hα : α ∈ Submodule.span ℤ (Irr H)) (hα0 : α ≠ 0)
    (h : ∀ χ ∈ Irr H, χ ∉ irrTrivialOn P → cfInner α χ = 0) :
    (Nat.card H : ℝ) - 1 ≤ ∑ x ∈ ({1} : Finset H)ᶜ, ‖α x‖ ^ 2 :=
  sum_norm_sq_compl_one_ge_of_mem_span_irrTrivialOn hP
    (mem_span_irrTrivialOn_of_cfInner_eq_zero hα h) hα0

end CFSG.FeitThompson
