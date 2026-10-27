module

public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSums
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.Wreathed.FourPointThreePairs

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.FourPointGaussianColumns

open scoped BigOperators Classical

variable {G : Type} [Group G] [Fintype G]

theorem eq_or_eq_conjLabel_of_inConjPair (basis : FiniteIrreducibleCharacterBasis G)
    {χ ψ : basis.index}
    (h : InConjPair (basis.representation χ).character (basis.representation ψ).character) :
    χ = ψ ∨ χ = conjLabel basis ψ := by
  rcases h with h | h
  · exact Or.inl (basis.distinct h)
  · exact Or.inr (conjLabel_eq_of_spec basis ψ χ fun g => congrFun h g).symm

theorem three_pairs_of_dichotomy (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (i : ℂ) (T U : basis.index → ℂ)
    (hTσ : ∀ χ, T (conjLabel basis χ) = starRingEnd ℂ (T χ))
    (hUσ : ∀ χ, U (conjLabel basis χ) = starRingEnd ℂ (U χ))
    (hdich : GaussianPairDichotomy basis B i T U)
    (heven : ∀ χ ∈ B, ∃ k : ℤ, imCoeff i (T χ) = 2 * k) :
    ∃ χ₁ χ₂ χ₃ : basis.index,
      [χ₁, conjLabel basis χ₁, χ₂, conjLabel basis χ₂, χ₃, conjLabel basis χ₃].Nodup ∧
      B.filter (fun χ => imCoeff i (U χ) ≠ 0) =
        {χ₁, conjLabel basis χ₁, χ₂, conjLabel basis χ₂, χ₃, conjLabel basis χ₃} ∧
      imCoeff i (U χ₁) = 1 ∧ imCoeff i (U χ₂) = 1 ∧ imCoeff i (U χ₃) = 1 ∧
      imCoeff i (T χ₁) = 4 ∧ imCoeff i (T χ₂) = -2 ∧ imCoeff i (T χ₃) = -2 ∧
      ∀ χ ∈ B, χ ∉ ({χ₁, conjLabel basis χ₁, χ₂, conjLabel basis χ₂, χ₃,
        conjLabel basis χ₃} : Finset basis.index) →
        imCoeff i (T χ) = 0 ∧ imCoeff i (U χ) = 0 := by
  obtain ⟨χ₁, h1B, χ₂, h2B, χ₃, h3B, h12, h13, h23, hU1, hU2, hU3, -, hUpairs, hD1, hD2, hD3,
    hcase⟩ := hdich
  obtain ⟨hT1, hT2, hT3, hTpairs⟩ : imCoeff i (T χ₁) = 4 ∧ imCoeff i (T χ₂) = -2 ∧
      imCoeff i (T χ₃) = -2 ∧ ∀ χ ∈ B, imCoeff i (T χ) ≠ 0 →
        InConjPair (basis.representation χ).character (basis.representation χ₁).character ∨
        InConjPair (basis.representation χ).character (basis.representation χ₂).character ∨
        InConjPair (basis.representation χ).character (basis.representation χ₃).character := by
    rcases hcase with ⟨-, hT2, -⟩ | h
    · exfalso
      obtain ⟨k, hk⟩ := heven χ₂ h2B
      rw [hT2] at hk
      have hk' : (2 * k : ℤ) = 1 := by exact_mod_cast hk.symm
      omega
    · exact h
  set σ := conjLabel basis with hσ
  have hUσ' : ∀ χ, imCoeff i (U (σ χ)) = -imCoeff i (U χ) := fun χ => by
    rw [hUσ, imCoeff_conj]
  have hTσ' : ∀ χ, imCoeff i (T (σ χ)) = -imCoeff i (T χ) := fun χ => by
    rw [hTσ, imCoeff_conj]
  have hpair : ∀ χ, IsDetectedPair basis B χ → σ χ ∈ B ∧ σ χ ≠ χ := fun χ hD =>
    ⟨(hD.2 (σ χ) (conjLabel_spec basis χ)).1, (hD.2 (σ χ) (conjLabel_spec basis χ)).2.1⟩
  obtain ⟨hσ1B, hσ1⟩ := hpair χ₁ hD1
  obtain ⟨hσ2B, hσ2⟩ := hpair χ₂ hD2
  obtain ⟨hσ3B, hσ3⟩ := hpair χ₃ hD3
  have hinj : ∀ {χ ψ}, χ ≠ ψ → σ χ ≠ σ ψ := fun h h' => h (conjLabel_injective basis h')
  have hsep : ∀ χ ψ, imCoeff i (U χ) = 1 → imCoeff i (U ψ) = 1 → χ ≠ σ ψ := by
    intro χ ψ hχ hψ h
    have h' := hUσ' ψ
    rw [← h, hχ, hψ] at h'
    norm_num at h'
  have hnodup : [χ₁, σ χ₁, χ₂, σ χ₂, χ₃, σ χ₃].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨hσ1.symm, h12, hsep χ₁ χ₂ hU1 hU2, h13, hsep χ₁ χ₃ hU1 hU3⟩,
      ⟨fun h => hsep χ₂ χ₁ hU2 hU1 h.symm, hinj h12, fun h => hsep χ₃ χ₁ hU3 hU1 h.symm,
        hinj h13⟩,
      ⟨hσ2.symm, h23, hsep χ₂ χ₃ hU2 hU3⟩, ⟨fun h => hsep χ₃ χ₂ hU3 hU2 h.symm, hinj h23⟩,
      hσ3.symm⟩
  have hfilter : B.filter (fun χ => imCoeff i (U χ) ≠ 0) =
      {χ₁, σ χ₁, χ₂, σ χ₂, χ₃, σ χ₃} := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hχB, hχU⟩
      rcases hUpairs χ hχB hχU with h | h | h
      · rcases eq_or_eq_conjLabel_of_inConjPair basis h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · rcases eq_or_eq_conjLabel_of_inConjPair basis h with h' | h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · rcases eq_or_eq_conjLabel_of_inConjPair basis h with h' | h'
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨h1B, by rw [hU1]; norm_num⟩
      · exact ⟨hσ1B, by rw [hUσ', hU1]; norm_num⟩
      · exact ⟨h2B, by rw [hU2]; norm_num⟩
      · exact ⟨hσ2B, by rw [hUσ', hU2]; norm_num⟩
      · exact ⟨h3B, by rw [hU3]; norm_num⟩
      · exact ⟨hσ3B, by rw [hUσ', hU3]; norm_num⟩
  refine ⟨χ₁, χ₂, χ₃, hnodup, hfilter, hU1, hU2, hU3, hT1, hT2, hT3, fun χ hχB hχnot => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hχnot
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hχnot
  refine ⟨?_, ?_⟩
  · by_contra h
    rcases hTpairs χ hχB h with h' | h' | h' <;>
      rcases eq_or_eq_conjLabel_of_inConjPair basis h' with h'' | h'' <;> contradiction
  · by_contra h
    have hmem : χ ∈ B.filter (fun χ => imCoeff i (U χ) ≠ 0) := Finset.mem_filter.mpr ⟨hχB, h⟩
    rw [hfilter] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h' | h' | h' | h' <;> contradiction

end CFSG.Wreathed.FourPointThreePairs
