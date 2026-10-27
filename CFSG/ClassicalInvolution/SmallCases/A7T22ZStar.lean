module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7FactsInputs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.A7T22

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Hat2A7
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_trivialOnQuot_of_twin (hΩ : HypOmegaGen Ω) {K L : Subgroup G} {z : G} (hL : L ∈ Ω)
    (hK : K ∈ Ω) (hLK : L ≠ K) (hzL : IsUniqueInvolution L z) (hzK : IsUniqueInvolution K z) :
    L ≤ trivialOnQuot K := fun _ ha =>
  ⟨Sec6Gen.le_normalizer_of_twin hΩ hL hK hLK hzL hzK ha, fun _ hx =>
    (Sec6Gen.comm_le_oddCore_of_twin hΩ hL hK hLK hzL hzK
      (Subgroup.commutator_mem_commutator ha hx)).2⟩

end CFSG.ClassicalInvolution.A7T22
