module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7E0
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CyclicFour
import CFSG.ClassicalInvolution.Q3.Q3T7M00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7E

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Perfect

variable {G : Type} [Group G] [Finite G]

theorem closure_odd_eq_of_perfect {K : Subgroup G} (hK : Group.IsPerfect ↥K) :
    Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K := by
  refine le_antisymm ((Subgroup.closure_le K).mpr fun x hx => hx.1) fun g hg => ?_
  have hperf : commutator (↥K ⧸ classicalInvolutionOddCore ↥K) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (classicalInvolutionOddCore ↥K))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  have hAtop : Subgroup.normalClosure {x : ↥K | Odd (orderOf x)} = ⊤ :=
    eq_top_of_forall_odd_orderOf_mem hperf _ fun x hx => Subgroup.subset_normalClosure hx
  have hgA : (⟨g, hg⟩ : ↥K) ∈ Subgroup.normalClosure {x : ↥K | Odd (orderOf x)} :=
    hAtop ▸ Subgroup.mem_top _
  have hle : Subgroup.normalClosure {x : ↥K | Odd (orderOf x)} ≤
      (Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)}).subgroupOf K := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨y.2, ?_⟩)
    have h1 : orderOf y = orderOf a := by
      rw [← hc]
      simpa using (MulAut.conj c).orderOf_eq a
    rw [Subgroup.orderOf_coe, h1]
    exact ha
  exact Subgroup.mem_subgroupOf.mp (hle hgA)

end Perfect

section Quasisimple

theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q :=
  CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.eq_top_or_le_center_of_isQuasisimple
    hQ hN

theorem eq_bot_of_odd_normal {Q : Type} [Group Q] [Finite Q] (hq : CFSG.Open.IsQuasisimple Q)
    (hZ : Nat.card (Subgroup.center Q) = 2) (N : Subgroup Q) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  rcases normal_eq_top_or_le_center hq (inferInstance : N.Normal) with h | h
  · exfalso
    have h1 : Nat.card N = Nat.card Q := by rw [h, Subgroup.card_top]
    have h2 : 2 ∣ Nat.card Q := hZ ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center Q)
    rw [← h1] at h2
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h2)
  · have h1 : Nat.card N ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le h
    have h2 : Nat.card N = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h3 | h3
      · exact h3
      · rw [h3] at hN
        exact absurd hN (by decide)
    exact (Subgroup.card_eq_one).mp h2

end Quasisimple

abbrev HM {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop := HypOmegaModU .twoA7 Ω

namespace HM

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem toGen [Finite G] (hΩ : HM Ω) : HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (t := .twoA7) trivial hΩ

instance [Finite G] : Coe (HM Ω) (HypOmegaGen Ω) := ⟨toGen⟩

theorem exists_uniqueInvolution [Finite G] (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ z : G, IsUniqueInvolution K z :=
  Sec6Gen.exists_uniqueInvolution hΩ.toGen hK

theorem isQuatSub_of_mem_RSet [Finite G] (hΩ : HM Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : IsQuatSub R :=
  Sec6Gen.isQuatSub_of_mem_RSet hΩ.toGen hR

theorem eight_le_of_mem_RSet [Finite G] (hΩ : HM Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : 8 ≤ Nat.card R :=
  Sec6Gen.eight_le_of_mem_RSet hΩ.toGen hR

theorem eq_of_le_of_le [Finite G] (hΩ : HM Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A)
    (hAK : A ≤ K) (hAJ : A ≤ J) : K = J :=
  Sec6Gen.eq_of_le_of_le hΩ.toGen hK hJ hA h4 hAK hAJ

theorem le_normalizer_of_le_centralizer [Finite G] (hΩ : HM Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hA3 : 3 ≤ Nat.card A) (hAc : A ≤ Subgroup.centralizer ({z} : Set G)) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_le_centralizer hΩ.toGen hK hJ hKJ hz hAJ hA2 hA3 hAc

theorem oddGen [Finite G] (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact closure_odd_eq_of_perfect (hz.perfect MemberType.not_isSolvableType_twoA7)

end HM

section Six3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_kPerp_of_twin (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) : K ∈ KPerp Ω L :=
  CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΩ hK hL hzK hzL

end Six3

section OddGen

variable {G : Type} [Group G]

theorem le_of_sq_mem_of_oddGen {K L : Subgroup G}
    (hK : Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K) (h : ∀ x ∈ K, x * x ∈ L) :
    K ≤ L :=
  CFSG.ClassicalInvolution.Q3.Q3T7M.le_of_sq_mem_of_oddGen hK h

end OddGen

end CFSG.ClassicalInvolution.Hat2A7E

namespace CFSG.ClassicalInvolution.Hat2A7E.Generic

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Uniform
open CFSG.Open

variable {Y : Type} [Group Y]

abbrev IsClassicalMember (L : Subgroup Y) (z : Y) : Prop :=
  IsClassicalMemberU .twoA7 L z

end CFSG.ClassicalInvolution.Hat2A7E.Generic

namespace CFSG.ClassicalInvolution.Hat2A7E.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Vocab

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

abbrev HypOmegaMod (Ω : Set (Subgroup G)) : Prop := HypOmegaGen Ω

abbrev L6_7 : Prop := Q3.Q3CP.L67Gen

theorem l6_7_proved : L6_7 := Q3.Q3CP.l67Gen

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

end Vocab

section Stand

structure EStand {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W : Subgroup G) : Prop where
  hyp : HM Ω
  below : Hat2A7.CITBelow2A7 (Nat.card G)
  mem : K ∈ Ω
  aEmpty : AEmpty Ω K
  twin : ∃ K' ∈ twinSet Ω K, K' ≠ K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W : Subgroup G}

theorem EStand.hypGen (h : EStand Ω K S R W) : HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (t := .twoA7) trivial h.hyp

theorem EStand.ofA7 (h : Hat2A7S.EStandA7 Ω K S R W) : EStand Ω K S R W where
  hyp := ⟨h.hyp.conjInvariant, fun L hL => by
    obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, IsClassicalMemberU.of2A7 hz⟩, h.hyp.omega4, h.hyp.omega5⟩
  below := h.below
  mem := h.mem
  aEmpty := h.aEmpty
  twin := h.twin
  hR := h.hR
  hW := h.hW

end Stand

@[expose] def Thm4Below (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
    HM Ω → classicalInvolutionOddCore G = ⊥ → (∀ K ∈ Ω, AEmpty Ω K) →
      ∀ K ∈ Ω, ∀ J ∈ Ω, (¬ ∃ g : G, conjSub g K = J) → Commutes K J

@[expose] def Thm2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)),
    HM Ω → classicalInvolutionOddCore G = ⊥ → (⨆ J ∈ Ω, J) = ⊤ → ∀ K ∈ Ω,
      (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
        ∀ z : G, IsUniqueInvolution K z → (∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ z ∈ N) →
          K.Normal

section ExactHyp

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem natCard_center_of_exact {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}
    (hz : IsClassicalMemberU .twoA7 L z) (hex : classicalInvolutionOddCore ↥L = ⊥) :
    Nat.card (Subgroup.center ↥L) = 2 := by
  have h2 := hz.natCard_center_eq_two
  let e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hex).trans QuotientGroup.quotientBot
  rw [← h2, ← Subgroup.map_center_eq e]
  exact Subgroup.card_map_of_injective e.injective

structure HypOmega (Ω : Set (Subgroup G)) : Prop where
  conjInvariant : ConjInvariant Ω
  classical : ∀ L ∈ Ω, ∃ z : G, IsClassicalMemberU .twoA7 L z
  exact : ExactMembers Ω
  omega4 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → Commutes K J)
  omega5 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
    (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set G)

theorem HypOmega.toModU (h : HypOmega Ω) : HypOmegaModU .twoA7 Ω where
  conjInvariant := h.conjInvariant
  classical := h.classical
  omega4 K hK J hJ hKJ := by
    refine ⟨(h.omega4 K hK J hJ hKJ).1, fun he => ?_⟩
    have hc := (h.omega4 K hK J hJ hKJ).2 he
    refine le_trans (Subgroup.commutator_le.mpr fun g hg x hx => ?_) bot_le
    have : g * x = x * g := hc g hg x hx
    simp [commutatorElement_def, this]
  omega5 := h.omega5

theorem HypOmega.toMod (h : HypOmega Ω) : HM Ω := h.toModU

theorem HypOmega.toGen [Finite G] (h : HypOmega Ω) :
    HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (t := .twoA7) trivial h.toModU

theorem HypOmega.commutes_of_twin [Finite G] (hΩ : HypOmega Ω) {K J : Subgroup G}
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

theorem HypOmega.natCard_center [Finite G] (hΩ : HypOmega Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Nat.card (Subgroup.center ↥K) = 2 := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact natCard_center_of_exact hz (hΩ.exact K hK)

theorem HypOmega.mul_self_eq_one_of_central [Finite G] (hΩ : HypOmega Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {w : G} (hw : w ∈ K) (hc : ∀ y ∈ K, w * y = y * w) : w * w = 1 := by
  have hmem : (⟨w, hw⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  have h1 := pow_card_eq_one' (G := ↥(Subgroup.center ↥K)) (x := ⟨⟨w, hw⟩, hmem⟩)
  rw [hΩ.natCard_center hK] at h1
  have h2 : w ^ 2 = 1 := by
    have := congrArg (fun x : ↥(Subgroup.center ↥K) => ((x : ↥K) : G)) h1
    simpa using this
  simpa [pow_two] using h2

theorem HypOmega.isQuasisimple [Finite G] (hΩ : HypOmega Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    CFSG.Open.IsQuasisimple ↥K := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  let e : ↥K ⧸ classicalInvolutionOddCore ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq (hΩ.exact K hK)).trans QuotientGroup.quotientBot
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hz.witness.1

end ExactHyp

end CFSG.ClassicalInvolution.Hat2A7E.Asc77
