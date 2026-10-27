module

import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {G : Type*} [Group G]

theorem exists_eq_one_or_eq_neg_one_of_sum_sq_eq_one {ι : Type*} [Fintype ι] {n : ι → ℤ}
    (h : ∑ i, n i ^ 2 = 1) : ∃ i₀, (n i₀ = 1 ∨ n i₀ = -1) ∧ ∀ i, i ≠ i₀ → n i = 0 := by
  classical
  obtain ⟨i₀, -, hi₀⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => sq_nonneg (n i))).1
    (by rw [h]; norm_num)
  have hrest : ∑ i ∈ Finset.univ.erase i₀, n i ^ 2 = 1 - n i₀ ^ 2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), h]
  have hzero : ∀ i ∈ Finset.univ.erase i₀, n i ^ 2 = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (n i)).1 ?_
    have h1 : 1 ≤ n i₀ ^ 2 := hi₀
    have hle : ∑ i ∈ Finset.univ.erase i₀, n i ^ 2 ≤ 0 := by rw [hrest]; linarith
    exact le_antisymm hle (Finset.sum_nonneg fun i _ => sq_nonneg (n i))
  have hsum0 : (0 : ℤ) = 1 - n i₀ ^ 2 := by rw [← hrest, Finset.sum_eq_zero hzero]
  refine ⟨i₀, ?_, fun i hi => ?_⟩
  · have hfac : (n i₀ - 1) * (n i₀ + 1) = 0 := by linarith
    rcases mul_eq_zero.1 hfac with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · have h2 := hzero i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
    nlinarith [sq_nonneg (n i)]

theorem mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one [Fintype G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (hf1 : cfInner f f = 1) : f ∈ signedIrr G := by
  classical
  have : Fintype (Irr G) := Fintype.ofFinite _
  obtain ⟨n, rfl⟩ := mem_span_Irr_iff_exists_intCast_sum.1 hf
  rw [cfInner_self_intCast_sum_Irr] at hf1
  have hsum : ∑ χ : Irr G, n χ ^ 2 = 1 := by exact_mod_cast hf1
  obtain ⟨χ₀, hχ₀, hrest⟩ := exists_eq_one_or_eq_neg_one_of_sum_sq_eq_one hsum
  have hfe : ∑ χ : Irr G, (n χ : ℂ) • ((χ : Irr G) : G → ℂ)
      = (n χ₀ : ℂ) • ((χ₀ : Irr G) : G → ℂ) :=
    Finset.sum_eq_single_of_mem χ₀ (Finset.mem_univ _)
      (fun b _ hb => by rw [hrest b hb]; simp)
  rw [hfe]
  exact mem_signedIrr_iff_exists_sign.2
    ⟨(n χ₀ : ℂ), by rcases hχ₀ with h | h <;> simp [h], _, χ₀.2, rfl⟩

theorem mem_Irr_or_neg_mem_Irr_of_mem_span_Irr_of_cfInner_self_eq_one [Fintype G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (hf1 : cfInner f f = 1) :
    f ∈ Irr G ∨ -f ∈ Irr G :=
  mem_signedIrr.1 (mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one hf hf1)

private theorem eq_of_mul_conj_eq_one' {ε δ : ℂ} (hδ : δ = 1 ∨ δ = -1) (h : ε * conj δ = 1) :
    ε = δ := by
  rcases hδ with rfl | rfl
  · simpa using h
  · have h' : -ε = 1 := by simpa using h
    linear_combination -h'

theorem sign_smul_Irr_inj [Finite G] {ε δ : ℂ} (hδ : δ = 1 ∨ δ = -1) {χ ψ : G → ℂ}
    (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G) (h : ε • χ = δ • ψ) : ε = δ ∧ χ = ψ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hcf : cfInner (ε • χ) (δ • ψ) = 1 := by
    rw [h, cfInner_self_of_mem_signedIrr]
    exact mem_signedIrr_iff_exists_sign.2 ⟨δ, hδ, ψ, hψ, rfl⟩
  rw [cfInner_smul_smul_of_mem_Irr _ _ hχ hψ] at hcf
  by_cases hχψ : χ = ψ
  · subst hχψ
    rw [if_pos rfl] at hcf
    exact ⟨eq_of_mul_conj_eq_one' hδ hcf, rfl⟩
  · rw [if_neg hχψ] at hcf
    exact absurd hcf (by norm_num)

theorem existsUnique_sign_smul_Irr_of_cfInner_self_eq_one [Fintype G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (hf1 : cfInner f f = 1) :
    ∃! p : ℂ × (G → ℂ), (p.1 = 1 ∨ p.1 = -1) ∧ p.2 ∈ Irr G ∧ f = p.1 • p.2 := by
  obtain ⟨ε, hε, χ, hχ, hfχ⟩ := mem_signedIrr_iff_exists_sign.1
    (mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one hf hf1)
  refine ⟨(ε, χ), ⟨hε, hχ, hfχ⟩, ?_⟩
  rintro ⟨δ, ψ⟩ ⟨hδ, hψ, hfψ⟩
  obtain ⟨h1, h2⟩ := sign_smul_Irr_inj hε hψ hχ (hfψ ▸ hfχ)
  exact Prod.ext h1 h2

theorem signedIrr_subset_span_Irr : signedIrr G ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)) := by
  intro f hf
  rcases mem_signedIrr.1 hf with h | h
  · exact Submodule.subset_span h
  · simpa using (Submodule.span ℤ (Irr G)).neg_mem (Submodule.subset_span h)

theorem mem_signedIrr_iff_mem_span_Irr_and_cfInner_self_eq_one [Fintype G] {f : G → ℂ} :
    f ∈ signedIrr G ↔ f ∈ Submodule.span ℤ (Irr G) ∧ cfInner f f = 1 :=
  ⟨fun hf => ⟨signedIrr_subset_span_Irr hf, cfInner_self_of_mem_signedIrr hf⟩,
    fun ⟨hf, hf1⟩ => mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one hf hf1⟩

end CFSG.FeitThompson
