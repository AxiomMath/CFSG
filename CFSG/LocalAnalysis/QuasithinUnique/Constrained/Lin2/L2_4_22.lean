module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem lemma2_4_22 (h8 : Lemma2_4_8) (h12 : Lemma2_4_12) (h14 : Lemma2_4_14)
    (h21 : Lemma2_4_21) : Lemma2_4_22 := by
  intro G _ _ T M H S L D n hcfg
  obtain ⟨⟨hTS, hTnS, hTnR⟩, -, -, -, ⟨B, hB⟩, -, -⟩ := h8 G T M H S L D n hcfg
  have : IsSimpleGroup G := hcfg.simple
  have hST : S ≤ T := hcfg.S_le_T
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hRT : thompsonJ S ≤ T := hRS.trans hST
  obtain ⟨t₁, ht₁T, ht₁S⟩ : ∃ t ∈ T, t ∉ S := by
    by_contra hcon
    exact hcfg.S_ne_T (le_antisymm hST fun x hx => by_contra fun hxS => hcon ⟨x, hx, hxS⟩)
  have hex : ∃ t ∈ T, t ∉ thompsonJ S ∧ t ^ 2 = 1 := by
    by_cases hRS' : thompsonJ S = S
    · have hsq : t₁ ^ 2 ∈ thompsonJ S := by
        rw [hRS']
        exact sq_mem_of_relIndex_two hTS ht₁T
      obtain ⟨i, hi, hi2⟩ := (h14 G T M H S L D n hcfg t₁ ht₁T ht₁S hsq).1
      have hiT : i ∈ T := by
        have : t₁ * (t₁⁻¹ * i) ∈ T := T.mul_mem ht₁T (hRT hi)
        simpa using this
      refine ⟨i, hiT, fun hiR => ht₁S ?_, hi2⟩
      have : i * (t₁⁻¹ * i)⁻¹ ∈ thompsonJ S := (thompsonJ S).mul_mem hiR ((thompsonJ S).inv_mem hi)
      have e : i * (t₁⁻¹ * i)⁻¹ = t₁ := by group
      rw [e] at this
      exact hRS this
    · have hF := (h12 G T M H S L D n hcfg B hB).1
      obtain ⟨-, hRF, hRFS, -, -⟩ := hF
      have hFbot : S ⊓ Subgroup.normalizer (B : Set G) ≠ ⊥ := by
        intro h
        rw [h, sup_bot_eq] at hRFS
        exact hRS' hRFS
      have hF2 : IsPGroup 2 (S ⊓ Subgroup.normalizer (B : Set G) : Subgroup G) :=
        hcfg.cs.sylow.isPGroup.to_le inf_le_left
      obtain ⟨f, hf, hf2, hf1⟩ := exists_involution_of_isPGroup hF2 hFbot
      refine ⟨f, hST hf.1, fun hfR => hf1 ?_, hf2⟩
      have : f ∈ thompsonJ S ⊓ (S ⊓ Subgroup.normalizer (B : Set G)) := ⟨hfR, hf⟩
      rw [hRF] at this
      simpa using this
  have hnoncyc : ¬ ∃ t₀ ∈ T, T = thompsonJ S ⊔ Subgroup.zpowers t₀ := by
    rintro ⟨t₀, -, hcyc⟩
    obtain ⟨t, htT, htR, ht2⟩ := hex
    obtain ⟨-, hfusR⟩ := h21 G T M H S L D n hcfg
    refine transfer_contradiction_cyclic hcfg.nonabelian hcfg.sylowT hRT hTnR hcyc htT htR ht2 ?_
    intro g hg
    have hi2 : (g⁻¹ * t * g) ^ 2 = 1 := by
      have : (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g := by simp only [pow_two]; group
      rw [this, ht2]; simp
    have e : (g⁻¹)⁻¹ * (g⁻¹ * t * g) * g⁻¹ = t := by group
    have := hfusR (g⁻¹ * t * g) hg hi2 g⁻¹ (by rw [e]; exact htT)
    rw [e] at this
    exact htR this
  refine ⟨hnoncyc, lt_of_le_of_ne hRS fun hRS' => hnoncyc ⟨t₁, ht₁T, ?_⟩⟩
  rw [hRS']
  exact eq_sup_zpowers_of_relIndex_two hST hTS ht₁T ht₁S

end CFSG.QuasithinUnique.Lin2
