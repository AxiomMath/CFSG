module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.T7F25

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

namespace Asc77

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

abbrev HypOmegaMod (Ω : Set (Subgroup G)) : Prop := HypOmegaGen Ω

theorem HypOmegaMod.exists_uniqueInvolution (hΩ : HypOmegaMod Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ z : G, IsUniqueInvolution K z :=
  Sec6Gen.exists_uniqueInvolution hΩ hK

theorem HypOmegaMod.isQuatSub_of_mem_RSet [Finite G] (hΩ : HypOmegaMod Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : IsQuatSub R :=
  Sec6Gen.isQuatSub_of_mem_RSet hΩ hR

theorem HypOmegaMod.eight_le_of_mem_RSet [Finite G] (hΩ : HypOmegaMod Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : 8 ≤ Nat.card R :=
  Sec6Gen.eight_le_of_mem_RSet hΩ hR

theorem HypOmegaMod.card_le_two_of_le_inf [Finite G] (hΩ : HypOmegaMod Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : Nat.card A ≤ 2 :=
  Sec6Gen.card_le_two_of_le_inf hΩ hK hJ hKJ hA hAK hAJ

theorem HypOmegaMod.le_normalizer_of_le_centralizer [Finite G] (hΩ : HypOmegaMod Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hA3 : 3 ≤ Nat.card A) (hAc : A ≤ Subgroup.centralizer ({z} : Set G)) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.HypOmegaMod.le_normalizer_of_le_centralizer hΩ hK hJ hKJ
    hz hAJ hA2 hA3 hAc

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

theorem HypOmegaMod.exists_data_of_mem_USet [Finite G] (hΩ : HypOmegaMod Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) :
    ∃ R ∈ RSet Ω, ∃ J ∈ Ω, IsSylow2In R J ∧ U ≤ R ∧ IsCyclic ↥U ∧
      Nat.card R = 2 * Nat.card U ∧ 4 ≤ Nat.card U :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.HypOmegaMod.exists_data_of_mem_USet hΩ hU

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

end Asc77

section Stand

namespace Asc77

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}

structure AscStand {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  hyp : HypOmegaGen Ω
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤
  key : CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.KeyOn Ω
  subn : ∀ L ∈ Ω, ∀ {z : G}, IsUniqueInvolution L z →
    IsSubnormal L (Subgroup.centralizer ({z} : Set G))
  nine3 : ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
    ∀ S : Subgroup G, IsSylow2In S (Subgroup.centralizer ({z} : Set G)) →
      ∀ U : Subgroup G, U ≤ S → IsElemAbelian2 U 2 → ∀ d ∈ U, d ≠ 1 →
        gamma1 U (S ⊓ ⨆ L ∈ twinSet Ω K, L) ≤ Subgroup.centralizer ({d} : Set G) →
          ∃ x ∈ K, orderOf x = 4 ∧ x * d = d * x

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

theorem omega_of_comm [Finite G] {W : Subgroup G} (c : Q3.Q3CL.Thompson.Ctx Ω W)
    (ρ σ : CFSG.ClassicalInvolution.Asc77.Thompson.Rep Ω W) (hne : ρ.K ≠ σ.K)
        (hcomm : ρ.img * σ.img = σ.img * ρ.img) :
    σ.K ∈ omegaNbr Ω ρ.K := by
  by_contra hnot
  exact c.noncomm ρ σ hne hnot hcomm

end P25

end CFSG.ClassicalInvolution.T7F25
