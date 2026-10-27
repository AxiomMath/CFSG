module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2
public import CFSG.ClassicalInvolution.Uniform.UStand
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.T7FU

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

structure HM {G : Type} [Group G] (T : MemberType) (Ω : Set (Subgroup G)) : Prop where
  toMod : HypOmegaModU T Ω
  toGen [Finite G] : HypOmegaGen Ω

namespace HM

variable {G : Type} [Group G] {T : MemberType} {Ω : Set (Subgroup G)}

theorem exists_uniqueInvolution [Finite G] (hΩ : HM T Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ z : G, IsUniqueInvolution K z :=
  Sec6Gen.exists_uniqueInvolution hΩ.toGen hK

theorem isQuatSub_of_mem_RSet [Finite G] (hΩ : HM T Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : IsQuatSub R :=
  Sec6Gen.isQuatSub_of_mem_RSet hΩ.toGen hR

theorem eight_le_of_mem_RSet [Finite G] (hΩ : HM T Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : 8 ≤ Nat.card R :=
  Sec6Gen.eight_le_of_mem_RSet hΩ.toGen hR

theorem center_two [Finite G] (hΩ : HM T Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) :
    ∀ w ∈ K, IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) →
      w = 1 ∨ w = z :=
  Sec6Gen.center_two hΩ.toGen hK hz

theorem card_le_two_of_le_inf [Finite G] (hΩ : HM T Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : Nat.card A ≤ 2 :=
  Sec6Gen.card_le_two_of_le_inf hΩ.toGen hK hJ hKJ hA hAK hAJ

theorem eq_of_le_of_le [Finite G] (hΩ : HM T Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A)
    (hAK : A ≤ K) (hAJ : A ≤ J) : K = J :=
  Sec6Gen.eq_of_le_of_le hΩ.toGen hK hJ hA h4 hAK hAJ

theorem comm_le_oddCore_of_twin [Finite G] (hΩ : HM T Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J :=
  Sec6Gen.comm_le_oddCore_of_twin hΩ.toGen hK hJ hKJ hzK hzJ

theorem exists_data_of_mem_USet [Finite G] (hΩ : HM T Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) :
    ∃ R ∈ RSet Ω, ∃ J ∈ Ω, IsSylow2In R J ∧ U ≤ R ∧ IsCyclic ↥U ∧
      Nat.card R = 2 * Nat.card U ∧ 4 ≤ Nat.card U :=
  Sec6Gen.exists_data_of_mem_USet hΩ.toGen hU

theorem eq_of_mem_USet [Finite G] (hΩ : HM T Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hUK : U ≤ K)
    (hUK' : U ≤ K') : K = K' :=
  Sec6Gen.eq_of_mem_USet hΩ.toGen hU hK hK' hUK hUK'

theorem conjInvariant (hΩ : HM T Ω) : ConjInvariant Ω := hΩ.toMod.conjInvariant

theorem classical (hΩ : HM T Ω) : ∀ L ∈ Ω, ∃ z : G, IsClassicalMemberU T L z :=
  hΩ.toMod.classical

end HM

end CFSG.ClassicalInvolution.T7FU
