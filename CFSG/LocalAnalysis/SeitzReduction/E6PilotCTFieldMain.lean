module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTField
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTField

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.Quasithin (perfectCore)

local instance e6PilotCTFieldMainNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem one_not_mem_nodes_high :
    (1 : Fin (Tag.rank .E6)) ∉ ({0, 2, 3, 4, 5} : Finset (Fin (Tag.rank .E6))) := by
  decide

section Normalizer

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem mem_normalizer_pieceSup {t : G} (ht : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer ((pieceSup e : Subgroup G) : Set G) :=
  F4Pilot.mem_normalizer_iSup fun J => le_normalizer_pieceCore e ht J.1

end Normalizer

end CFSG.SeitzReduction.E6Pilot
