module

public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3T7F25M0

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

namespace Asc77

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

abbrev HypOmegaMod (Ω : Set (Subgroup G)) : Prop := HypOmegaGen Ω

abbrev PartIHyp (Ω : Set (Subgroup G)) : Prop := Q3.Q3CL.PartIHypG Ω

theorem HypOmegaMod.exists_uniqueInvolution (hΩ : HypOmegaMod Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ z : G, IsUniqueInvolution K z :=
  Sec6Gen.exists_uniqueInvolution hΩ hK

theorem HypOmegaMod.isQuatSub_of_mem_RSet [Finite G] (hΩ : HypOmegaMod Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : IsQuatSub R :=
  Sec6Gen.isQuatSub_of_mem_RSet hΩ hR

theorem HypOmegaMod.card_le_two_of_le_inf [Finite G] (hΩ : HypOmegaMod Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : Nat.card A ≤ 2 :=
  Sec6Gen.card_le_two_of_le_inf hΩ hK hJ hKJ hA hAK hAJ

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

theorem HypOmegaMod.isPGroup_of_mem_USet [Finite G] (hΩ : HypOmegaMod Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : IsPGroup 2 U :=
  Sec6Gen.isPGroup_of_mem_USet hΩ hU

abbrev L6_7 : Prop := Q3.Q3CP.L67Gen

theorem l6_7_proved : L6_7 := Q3.Q3CP.l67Gen

abbrev L6_11 : Prop := Sec6Gen.L6_11Gen

theorem l6_11_proved : L6_11 := Sec6Gen.l6_11Gen

end Asc77

section Stand

namespace Asc77

class CoreLike (G : Type) [Group G] : Prop where
  oddCore_eq_bot : CFSG.oddCore G = ⊥
  center_eq_bot : Subgroup.center G = ⊥
  fstar_simple : IsSimpleGroup ↥(genFittingFStar G)
  fstar_nonab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a

end Asc77

namespace Asc77

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}

structure AscStand {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  hyp : HypOmegaGen Ω
  cls : Q3.Q3CL.ClassicalClause Ω
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤
  card8 : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → Nat.card ↥P = 8
  gen2 : ∀ J ∈ Ω, ∀ N : Subgroup G,
    (∀ x ∈ J, IsPGroup 2 ↥(Subgroup.zpowers x) → x ∈ N) → J ≤ N

theorem _root_.CFSG.ClassicalInvolution.Q8P.Asc77.AscStand.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} (h : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K) :
    CFSG.ClassicalInvolution.T7F25.Asc77.AscStand Ω K where
  hyp := h.hyp
  aEmpty := h.aEmpty
  mem := h.mem
  trans := h.trans
  gen := h.gen
  key := Q3.Q3CL.Sec7.l7_1Key ⟨h.hyp, h.cls, h.aEmpty⟩
  subn := fun _ hL _ hz => h.cls.isSubnormal_of_uniqueInvolution hL hz
  nine3 := Q3.Q3CL.l9_3 ⟨h.hyp, h.cls, h.aEmpty⟩

end Asc77

end Stand

namespace P25

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_orderOf_eq_four_of_mem_RSet [Finite G] (hΩ : HypOmegaGen Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : ∃ u ∈ R, orderOf u = 4 :=
  CFSG.ClassicalInvolution.T7F25.P25.exists_orderOf_eq_four_of_mem_RSet hΩ hR

end P25

end CFSG.ClassicalInvolution.Q8P
