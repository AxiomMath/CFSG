module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbal

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G]

theorem triple_facts {a x : G} {J : Subgroup G} (htri : GSUnbalancingTriple a x J) :
    x * x = 1 ∧ ⁅J, J⁆ = J ∧
      closure {y | ∃ j ∈ J, ∃ d ∈ ({x} : Set G), y = j⁻¹ * d⁻¹ * j * d} = J ∧
      ∀ d ∈ ((pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ⊓
        centralizer ({a} : Set G) : Subgroup G),
        d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype := by
  obtain ⟨-, hxo, -, hJa, hJc, hxJ, -⟩ := htri
  refine ⟨by rw [← pow_two, ← hxo, pow_orderOf_eq_one], commutator_eq_of_isPComponent hJa hJc,
    ?_, fun d hd => (mem_inf.mp hd).1⟩
  have hset : {y | ∃ j ∈ J, ∃ d ∈ ({x} : Set G), y = j⁻¹ * d⁻¹ * j * d} =
      {y | ∃ j ∈ J, y = j⁻¹ * x⁻¹ * j * x} := by
    ext y
    simp
  rw [hset]
  exact hxJ

theorem l34UnbalancingFourFact :
    L34UnbalancingFourFact := by
  intro G _ _ a x J F htri hcase hFN hF2 hxF hFo hFK hrk
  obtain ⟨hx2, hJ, hxJ', hDo⟩ := triple_facts htri
  have hxN : x ∈ normalizer (J : Set G) := mem_normalizer_of_closure hxJ' (Set.mem_singleton x)
  have hDJ := htri.2.2.2.2.2.2
  rcases hcase with h5 | h7 | hL
  · obtain ⟨n, M, hF⟩ := exists_l2Model (J := J) (Or.inl h5)
    exact four_l2 M hF hxN (rhoM_outer M hF hxN hx2 hxJ' hDJ hDo) hFN hF2 hFK hrk
  · obtain ⟨n, M, hF⟩ := exists_l2Model (J := J) (Or.inr h7)
    exact four_l2 M hF hxN (rhoM_outer M hF hxN hx2 hxJ' hDJ hDo) hFN hF2 hFK hrk
  · have hU := l34UnbalancingUnitaryStep G a x J htri hL
    exact four_l34 hJ hL hU hFN hF2 hxF hFo hFK hrk

end CFSG.ComponentClassification.GrSLit.L34Facts
