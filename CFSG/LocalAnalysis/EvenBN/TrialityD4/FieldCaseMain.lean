module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseCyclic
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseProductProp
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoMainSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

theorem trialityD4FieldAutomorphismCase_of_productFieldCase (hP : TrialityD4ProductFieldCase) :
    TrialityD4FieldAutomorphismCase := by
  intro G _ _ L f t h d hf hfe hlay _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hPp, -, htN, -, -, -, -⟩ := h.yamada_5_32_of_layerHyp d hlay
  have hQ2 : IsPGroup 2 (yamadaP d t ⊔ zpowers t : Subgroup G) :=
    hPp.to_sup_of_normal_left' (IsPGroup.of_card (n := 1) (by rw [h.card_zpowers_t, pow_one]))
      ((zpowers_le).2 htN)
  set N : Subgroup G := normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G) with hN
  have hQN : yamadaP d t ⊔ zpowers t ≤ N := le_normalizer
  obtain ⟨B₀, hB₀⟩ := (hQ2.comap_subtype (K := N)).exists_le_sylow
  have hB : IsSylowOf 2 (B₀.map N.subtype) N := ⟨B₀, rfl⟩
  have hQB : yamadaP d t ⊔ zpowers t ≤ B₀.map N.subtype := fun x hx =>
    ⟨⟨x, hQN hx⟩, hB₀ (mem_subgroupOf.2 hx), rfl⟩
  by_cases hcyc : ∃ x ∈ B₀.map N.subtype, B₀.map N.subtype = yamadaP d t ⊔ zpowers x
  · exact false_of_cyclic_quotient h d hlay _ hB hQB hcyc
  · exact hP G L f t h d hf hlay fun hfield =>
      hcyc (isCyclic_of_layerHypFieldAlt h d hf hfe hlay _ hB hQB hfield)

end CFSG.LocalAnalysis.EvenBN.TrialityD4
