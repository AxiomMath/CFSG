module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Part1b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_omegaNbr_of_trivialOnQuotGen (hΩ : HypOmegaGen Ω) {K J : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hJ : J ∈ Ω) (hne : J ≠ K)
    (htq : z ∈ trivialOnQuot J) : J ∈ omegaNbr Ω K := by
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one hz.sq
  obtain ⟨R, hR, hRc⟩ :=
    AscE184Sect.exists_isSylow2In_centralizer hz2 (ExactLayer.commutator_zpowers_le_iff.mpr htq)
  have hRc' : R ≤ Subgroup.centralizer ({z} : Set G) := by
    rwa [centralizer_zpowers_eq_singleton'] at hRc
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hR
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
  exact ⟨hJ, hne, R, hRset, hR.1,
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ hne.symm hz hR.1 hR.2.1 (by omega) hRc'⟩

end Part1b

end CFSG.ClassicalInvolution.Q3.Q3T6D
