module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7P1Th
public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7M

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

namespace Asc77

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

abbrev HypOmegaMod (Ω : Set (Subgroup G)) : Prop := HypOmegaGen Ω

theorem HypOmegaMod.isQuatSub_of_mem_RSet [Finite G] (hΩ : HypOmegaMod Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : IsQuatSub R :=
  Sec6Gen.isQuatSub_of_mem_RSet hΩ hR

theorem HypOmegaMod.eq_of_le_of_le [Finite G] (hΩ : HypOmegaMod Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A)
    (hAK : A ≤ K) (hAJ : A ≤ J) : K = J :=
  Sec6Gen.eq_of_le_of_le hΩ hK hJ hA h4 hAK hAJ

theorem HypOmegaMod.comm_le_oddCore_of_twin [Finite G] (hΩ : HypOmegaMod Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J :=
  Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hzK hzJ

theorem HypOmegaMod.le_normalizer_of_twin [Finite G] (hΩ : HypOmegaMod Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : K ≤ Subgroup.normalizer (J : Set G) :=
  Sec6Gen.le_normalizer_of_twin hΩ hK hJ hKJ hzK hzJ

theorem HypOmegaMod.commutes_of_twin_of_isPGroup [Finite G] (hΩ : HypOmegaMod Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {A B : Subgroup G}
    (hA : A ≤ K) (hB : B ≤ J) (hAB : IsPGroup 2 ↥(A ⊔ B)) : Commutes A B :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.HypOmegaMod.commutes_of_twin_of_isPGroup hΩ hK hJ hKJ hzK
    hzJ hA hB hAB

end Asc77

section Stand

namespace Asc77

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}

structure AscStand {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop extends Hat2A7S.Std2A7 Ω K where
  modU : HypOmegaModU .twoA7 Ω
  cls : Hat2A7P1.ClassicalClause8 Ω

theorem AscStand.of_std2A7 (h : Hat2A7S.Std2A7 Ω K) :
    AscStand Ω K :=
  { h with
    modU := ⟨h.hyp.conjInvariant, fun L hL => by
      obtain ⟨z, hz⟩ := h.classical L hL
      exact ⟨z, IsClassicalMemberU.of2A7 hz⟩, h.hyp.omega4, h.hyp.omega5⟩
    cls := (Hat2A7S.partIHypG8_of_std2A7 h).cls }

end Asc77

end Stand

namespace P25

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_orderOf_eq_four_of_mem_RSet [Finite G] (hΩ : HypOmegaGen Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : ∃ u ∈ R, orderOf u = 4 := by
  obtain ⟨k, -, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  refine ⟨((e.symm (QuaternionGroup.xa 0) : ↥R) : G), (e.symm _).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]

end P25

end CFSG.ClassicalInvolution.Hat2A7M
