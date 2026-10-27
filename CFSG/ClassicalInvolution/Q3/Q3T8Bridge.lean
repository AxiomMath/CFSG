module

public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuGraph

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

namespace Generic

abbrev IsClassicalMember {Y : Type} [Group Y] (L : Subgroup Y) (z : Y) : Prop :=
  IsClassicalMemberU (.sl2 3 1) L z

abbrev CITBelowU (n : ℕ) : Prop := CITBelowT (.sl2 3 1) n

end Generic

namespace Asc77

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

abbrev HypOmegaMod (Ω : Set (Subgroup G)) : Prop := HypOmegaGen Ω

abbrev PartIHyp (Ω : Set (Subgroup G)) : Prop := Q3CL.PartIHypG Ω

theorem HypOmegaMod.exists_uniqueInvolution (hΩ : HypOmegaMod Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ z : G, IsUniqueInvolution K z :=
  Sec6Gen.exists_uniqueInvolution hΩ hK

theorem HypOmegaMod.isQuatSub_of_mem_RSet [Finite G] (hΩ : HypOmegaMod Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : IsQuatSub R :=
  Sec6Gen.isQuatSub_of_mem_RSet hΩ hR

theorem HypOmegaMod.eight_le_of_mem_RSet [Finite G] (hΩ : HypOmegaMod Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : 8 ≤ Nat.card R :=
  Sec6Gen.eight_le_of_mem_RSet hΩ hR

theorem HypOmegaMod.center_two [Finite G] (hΩ : HypOmegaMod Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) :
    ∀ w ∈ K, IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) →
      w = 1 ∨ w = z :=
  Sec6Gen.center_two hΩ hK hz

theorem HypOmegaMod.exists_noncentral [Finite G] (hΩ : HypOmegaMod Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A) (hA3 : 3 ≤ Nat.card A) :
    ∃ v ∈ A, ¬ ∀ w ∈ J, v * w = w * v :=
  Sec6Gen.exists_noncentral hΩ hJ hAJ hA2 hA3

theorem HypOmegaMod.card_le_two_of_le_inf [Finite G] (hΩ : HypOmegaMod Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : Nat.card A ≤ 2 :=
  Sec6Gen.card_le_two_of_le_inf hΩ hK hJ hKJ hA hAK hAJ

theorem HypOmegaMod.eq_of_le_of_le [Finite G] (hΩ : HypOmegaMod Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A)
    (hAK : A ≤ K) (hAJ : A ≤ J) : K = J :=
  Sec6Gen.eq_of_le_of_le hΩ hK hJ hA h4 hAK hAJ

theorem HypOmegaMod.le_normalizer_of_le_centralizer [Finite G] (hΩ : HypOmegaMod Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hA3 : 3 ≤ Nat.card A) (hAc : A ≤ Subgroup.centralizer ({z} : Set G)) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ hKJ hz hAJ hA2 hA3 hAc

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
  Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hJ hKJ hzK hzJ hA hB hAB

theorem HypOmegaMod.exists_data_of_mem_USet [Finite G] (hΩ : HypOmegaMod Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) :
    ∃ R ∈ RSet Ω, ∃ J ∈ Ω, IsSylow2In R J ∧ U ≤ R ∧ IsCyclic ↥U ∧
      Nat.card R = 2 * Nat.card U ∧ 4 ≤ Nat.card U :=
  Sec6Gen.exists_data_of_mem_USet hΩ hU

theorem HypOmegaMod.isPGroup_of_mem_USet [Finite G] (hΩ : HypOmegaMod Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : IsPGroup 2 U :=
  Sec6Gen.isPGroup_of_mem_USet hΩ hU

theorem HypOmegaMod.exists_member_of_mem_USet [Finite G] (hΩ : HypOmegaMod Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : ∃ K ∈ Ω, U ≤ K :=
  Sec6Gen.exists_member_of_mem_USet hΩ hU

theorem HypOmegaMod.eq_of_mem_USet [Finite G] (hΩ : HypOmegaMod Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hUK : U ≤ K)
    (hUK' : U ≤ K') : K = K' :=
  Sec6Gen.eq_of_mem_USet hΩ hU hK hK' hUK hUK'

abbrev L6_2 : Prop := Sec6Gen.L6_2Gen

theorem l6_2 : L6_2 := Sec6Gen.l6_2Gen

abbrev L6_7 : Prop := Q3CP.L67Gen

theorem l6_7_proved : L6_7 := Q3CP.l67Gen

abbrev L6_10 : Prop := Sec6Gen.L6_10Gen

theorem l6_10_proved : L6_10 := Sec6Gen.l6_10Gen

abbrev L6_11 : Prop := Sec6Gen.L6_11Gen

theorem l6_11_proved : L6_11 := Sec6Gen.l6_11Gen

abbrev L6_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod Ω →
    ∀ S : Sylow 2 G,
      (∃ η ∈ etaSet Ω (S : Subgroup G), ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧
      ∀ η ∈ etaSet Ω (S : Subgroup G), (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) →
        (∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x) ∧
          {U | U ∈ USet Ω ∧ U ≤ ⨆ V ∈ η, V} = η

theorem l6_9_proved : L6_9 := fun _ _ _ _ hΩ S =>
  ⟨Sec6Gen.exists_invariant_mem_etaSet hΩ S, fun _ hη hinv =>
    Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hη hinv⟩

theorem thompsonGraphAll (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G))
    (hP : PartIHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) (hne : dComp Ω K ≠ dstarComp Ω K)
    {W : Subgroup G} (hW : W ∈ WSet Ω) : ¬ DbarConnected Ω W :=
  Q3T6.Mu.thompsonGraphAll hP hK hne hW

end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.HypOmegaGen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

alias exists_uniqueInvolution := Sec6Gen.exists_uniqueInvolution
alias isQuatSub_of_mem_RSet := Sec6Gen.isQuatSub_of_mem_RSet
alias eight_le_of_mem_RSet := Sec6Gen.eight_le_of_mem_RSet
alias center_two := Sec6Gen.center_two
alias exists_noncentral := Sec6Gen.exists_noncentral
alias card_le_two_of_le_inf := Sec6Gen.card_le_two_of_le_inf
alias eq_of_le_of_le := Sec6Gen.eq_of_le_of_le
alias le_normalizer_of_le_centralizer := Sec6Gen.le_normalizer_of_le_centralizer
alias comm_le_oddCore_of_twin := Sec6Gen.comm_le_oddCore_of_twin
alias le_normalizer_of_twin := Sec6Gen.le_normalizer_of_twin
alias commutes_of_twin_of_isPGroup := Sec6Gen.commutes_of_twin_of_isPGroup
alias exists_data_of_mem_USet := Sec6Gen.exists_data_of_mem_USet
alias isPGroup_of_mem_USet := Sec6Gen.isPGroup_of_mem_USet
alias exists_member_of_mem_USet := Sec6Gen.exists_member_of_mem_USet
alias eq_of_mem_USet := Sec6Gen.eq_of_mem_USet

end CFSG.ClassicalInvolution.Disconnected.AschTight.HypOmegaGen
