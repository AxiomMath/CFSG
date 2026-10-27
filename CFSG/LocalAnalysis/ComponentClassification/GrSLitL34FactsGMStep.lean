module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsGMFixed

public section

namespace CFSG.ComponentClassification.GrSLit.L34GM

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem step_of_gsWeakCorr (hS : SchreierFor Blueprint.Catalog)
    (hCT : L34ProperFixedCenterTrivial) (hPFS : L34ProperFixedSimpleRank)
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} {L M : Subgroup G}
    (h : GSWeakCorr a L b M) (hbZ : b ∉ center G) (htype : IsL34Type (L ⧸ Open.fusionZStar L))
    (hidx : (pPrimeCore 2 ↥L).index = 322560) :
    Nonempty (L ⧸ Open.fusionZStar L ≃* M ⧸ Open.fusionZStar M) ∧
      (pPrimeCore 2 ↥M).index = 322560 := by
  obtain ⟨ha, -, hab, -, -, hMb, hM, -, -, -⟩ := id h
  obtain ⟨hTN, hTpc, ⟨φ⟩⟩ := gsFixedLayer_isPComponent_of_gsWeakCorr hS hK h hbZ
  have hTL : (pPrimeCore 2 (gsFixedLayer L b)).index = (pPrimeCore 2 L).index := by
    rw [index_eq_card, index_eq_card]
    exact Nat.card_congr φ.toEquiv
  obtain ⟨hidxle, -, -⟩ := UGSChain.orbit_fixed_component_comparison ha hab hMb hM hTN hTpc
  rcases gsWeakCorr_type_dichotomy hS hK h hbZ with he | ⟨hMa, hTM, hTp, hlt, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    refine ⟨⟨e⟩, le_antisymm ?_ ?_⟩
    · exact index_le (UnbalancedCorr.commutator_eq_of_isPComponent hMb hM)
        (LieType.CurtisTits.lieModel_of_mulEquiv e htype)
    · rw [← hidx, ← hTL]
      exact hidxle
  · exfalso
    have hbtop : centralizer ({b} : Set G) ≠ ⊤ := fun htop =>
      hbZ (mem_center_iff.mpr fun g => mem_centralizer_singleton_iff.mp (htop ▸ mem_top g))
    exact false_of_proper_fixed_index hCT hPFS hK ha hbtop hMb hM hMa hTM hTp hlt
      (LieType.CurtisTits.lieModel_of_mulEquiv e htype) (hTL.trans hidx)

end CFSG.ComponentClassification.GrSLit.L34GM
