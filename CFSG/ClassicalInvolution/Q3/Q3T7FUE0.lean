module

public import CFSG.ClassicalInvolution.Q3.Q3T7FU0
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.AscSteps185

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.T7FU

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77

variable {T : MemberType}

namespace HM

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

instance [Finite G] : CoeOut (HM T Ω) (HypOmegaGen Ω) := ⟨fun h => h.toGen⟩

theorem le_normalizer_of_le_centralizer [Finite G] (hΩ : HM T Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hA3 : 3 ≤ Nat.card A) (hAc : A ≤ Subgroup.centralizer ({z} : Set G)) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_le_centralizer hΩ.toGen hK hJ hKJ hz hAJ hA2 hA3 hAc

theorem le_normalizer_of_twin [Finite G] (hΩ : HM T Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : K ≤ Subgroup.normalizer (J : Set G) :=
  Sec6Gen.le_normalizer_of_twin hΩ.toGen hK hJ hKJ hzK hzJ

theorem commutes_of_twin_of_isPGroup [Finite G] (hΩ : HM T Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {A B : Subgroup G}
    (hA : A ≤ K) (hB : B ≤ J) (hAB : IsPGroup 2 ↥(A ⊔ B)) : Commutes A B :=
  Sec6Gen.commutes_of_twin_of_isPGroup hΩ.toGen hK hJ hKJ hzK hzJ hA hB hAB

theorem isPGroup_of_mem_USet [Finite G] (hΩ : HM T Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : IsPGroup 2 U :=
  Sec6Gen.isPGroup_of_mem_USet hΩ.toGen hU

theorem isSylow2In_of_mem_RSet_of_le [Finite G] (hΩ : HM T Ω) {K R : Subgroup G} (hK : K ∈ Ω)
    (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have h8 := hΩ.eight_le_of_mem_RSet hR
  have hJK : K = J := hΩ.eq_of_le_of_le hK hJ hRJ.2.1 (by omega) hRK hRJ.1
  exact hJK ▸ hRJ

theorem exists_orderOf_eq_four_of_mem_RSet [Finite G] (hΩ : HM T Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : ∃ u ∈ R, orderOf u = 4 := by
  have hquat := hΩ.isQuatSub_of_mem_RSet hR
  obtain ⟨C, hCR, hC, hcard, -⟩ := hquat.exists_cyclic_max
  obtain ⟨J, -, -, hR2, -⟩ := mem_RSet_iff.mp hR
  have h8 := hquat.eight_le
  obtain ⟨x, hxC, hx⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic (hR2.to_le hCR) hC
    (by omega)
  exact ⟨x, hCR hxC, hx⟩


theorem omega5 (hΩ : HM T Ω) : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z →
    ∀ v ∈ J, (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set G) :=
  hΩ.toMod.omega5

theorem exists_orderOf_four_of_mem [Finite G] (hΩ : HM T Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ u ∈ K, orderOf u = 4 := by
  obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
  obtain ⟨u, huR, hu⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hR
  exact ⟨u, hRK.1 huR, hu⟩

end HM

namespace Asc77

section Stand

structure EStand {G : Type} [Group G] [Finite G] (T : MemberType) (Ω : Set (Subgroup G))
    (K : Subgroup G) (S : Sylow 2 G) (R W : Subgroup G) : Prop where
  hyp : HM T Ω
  mem : K ∈ Ω
  aEmpty : AEmpty Ω K
  twin : ∃ K' ∈ twinSet Ω K, K' ≠ K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

structure MinCex {G : Type} [Group G] [Finite G] (T : MemberType) (Ω : Set (Subgroup G))
    (K : Subgroup G) (S : Sylow 2 G) (R W H : Subgroup G) : Prop where
  stand : EStand T Ω K S R W
  hyp : EHyp Ω K W H
  proper : H ≠ ⊤

@[expose] def E18_6At (MT : MemberType) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G) (R W H : Subgroup G),
    MinCex MT Ω K S R W H → classicalInvolutionOddCore G = ⊥ ∧
      ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
        Subgroup.centralizer (F : Set G) = ⊥

@[expose] def E187E4CAt (MT : MemberType) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex MT Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → R' ≤ (S : Subgroup G) →
        ∀ A : Subgroup G, IsPGroup 2 A → (∃ w : G, w ≠ 1 ∧ w * w = 1 ∧ A = Subgroup.zpowers w) → R
            ⊔ R' ≤ Subgroup.centralizer (A : Set G) →
          Subgroup.centralizer (A : Set G) ≠ ⊤ →
          IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G))
            (Subgroup.centralizer (A : Set G)) → Subgroup.centralizer (A : Set G) ≤ H


structure HypOmega {G : Type} [Group G] (T : MemberType) (Ω : Set (Subgroup G)) : Prop where
  conjInvariant : ConjInvariant Ω
  classical : ∀ L ∈ Ω, ∃ z : G, IsClassicalMemberU T L z
  exact : ExactMembers Ω
  omega4 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → Commutes K J)
  omega5 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
    (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set G)
  toGen [Finite G] : HypOmegaGen Ω

theorem HypOmega.toModU {G : Type} [Group G] {Ω : Set (Subgroup G)} (h : HypOmega T Ω) :
    HypOmegaModU T Ω where
  conjInvariant := h.conjInvariant
  classical := h.classical
  omega4 K hK J hJ hKJ := by
    refine ⟨(h.omega4 K hK J hJ hKJ).1, fun he => ?_⟩
    have hc := (h.omega4 K hK J hJ hKJ).2 he
    refine le_trans (Subgroup.commutator_le.mpr fun g hg x hx => ?_) bot_le
    have : g * x = x * g := hc g hg x hx
    simp [commutatorElement_def, this]
  omega5 := h.omega5

theorem HypOmega.toMod {G : Type} [Group G] {Ω : Set (Subgroup G)} (h : HypOmega T Ω) :
    HM T Ω :=
  ⟨h.toModU, h.toGen⟩

theorem HypOmega.commutes_of_twin {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmega T Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : Commutes K J := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ J) (x := z) ⟨hzK.mem, hzJ.mem⟩
    rwa [hz2] at this
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have h1 := one_le_padicValNat_of_dvd hN hdvd
  obtain ⟨h2, h3⟩ := hΩ.omega4 K hK J hJ hKJ
  exact h3 (le_antisymm h2 h1)

end Stand

end Asc77

end CFSG.ClassicalInvolution.T7FU
