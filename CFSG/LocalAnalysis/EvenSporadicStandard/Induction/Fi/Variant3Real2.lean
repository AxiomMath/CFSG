module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Pair

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup

section Certificates


theorem fi23Transpositions_real : Fi23Transpositions := by
  intro G _ _ K hK
  refine ⟨?_, ?_⟩
  · obtain ⟨_, u₀, _, hu, _⟩ := exists_fiLoc_pair_of_isSporadic_fi23 hK (le_refl K)
    exact ⟨u₀, hu⟩
  · intro u hu
    obtain ⟨huK, hu2, hcard⟩ := hu
    obtain ⟨e⟩ := hK
    let ψ : ↥K ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
    have h1 : orderOf (ψ ⟨u, huK⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hu2]
    have h2 : Nat.card ↥(centralizer ({ψ ⟨u, huK⟩} : Set CFSG.Sporadic.Fi23.J)) =
        129123503308800 := by
      rw [← @fi23_card_inf_centralizer_eq G CFSG.Sporadic.Fi23.J _ (inferInstance) K ψ u huK]
      exact hcard
    exact @isQuasisimple_inf_centralizer_of_isConj G CFSG.Sporadic.Fi23.J _ (inferInstance) K ψ u
      huK CFSG.Sporadic.Fi23.d (fi23J_isConj_d_of_card h1 h2) isQuasisimple_centralizer_d

end Certificates

end CFSG.EvenSporadicStandard.Induction.Fi.V3
