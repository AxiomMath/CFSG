module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCz
public import CFSG.Quasithin.Recognition.J2RecDefs

public section

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

namespace CFSG.ComponentClassification.RankTwoAltFive

theorem quasithin_isQ8D8 {G : Type*} [Group G] [Finite G] {N : Subgroup G} (h : IsQ8D8 N) :
    CFSG.Quasithin.IsQ8D8 N := by
  obtain ⟨Q, D, ⟨eQ⟩, ⟨eD⟩, hcomm, hsup, -⟩ := id h
  have hQN : Q ≤ N := hsup ▸ le_sup_left
  have hDN : D ≤ N := hsup ▸ le_sup_right
  refine ⟨h.facts.1, Q.subgroupOf N, D.subgroupOf N, ⟨fun a ha => ?_, ?_⟩,
    ⟨(subgroupOfEquivOfLe hQN).trans eQ⟩, ⟨(subgroupOfEquivOfLe hDN).trans eD⟩⟩
  · exact mem_centralizer_iff.mpr fun b hb => Subtype.ext (hcomm _ ha _ hb).symm
  · rw [← subgroupOf_sup hQN hDN, hsup, subgroupOf_self]

theorem involutionClassCount_eq_two {G : Type} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (ha1 : a ≠ 1) (hb : b ^ 2 = 1) (hb1 : b ≠ 1) (hab : ¬ IsConj a b)
    (hcover : ∀ x : G, x ^ 2 = 1 → x ≠ 1 → IsConj a x ∨ IsConj b x) :
    CFSG.Quasithin.involutionClassCount G = 2 := by
  have hset : {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧ ConjClasses.mk x = c} =
      {ConjClasses.mk a, ConjClasses.mk b} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx2, hx1, rfl⟩
      rcases hcover x hx2 hx1 with h | h
      · exact Or.inl (ConjClasses.mk_eq_mk_iff_isConj.mpr h).symm
      · exact Or.inr (ConjClasses.mk_eq_mk_iff_isConj.mpr h).symm
    · rintro (rfl | rfl)
      · exact ⟨a, ha, ha1, rfl⟩
      · exact ⟨b, hb, hb1, rfl⟩
  rw [CFSG.Quasithin.involutionClassCount, hset]
  exact Set.ncard_pair fun h => hab (ConjClasses.mk_eq_mk_iff_isConj.mp h)

namespace Setting310

variable {G : Type} [Group G] [Finite G]
variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem isTypeH2_of_eps_one
    (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} {Q : Subgroup G} (hQ : QFacts (S : Subgroup G) V₀ z Q) :
    CFSG.Quasithin.IsTypeH2 G z := by
  obtain ⟨hpCore, hchar, hquot, hwc⟩ := h.centralizer_facts_of_eps_one hP hPC hIIa hGold hGs
    hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv S hPS hQ
  refine ⟨by rw [sq]; exact h.mul_self (h.V₀_le hQ.z_mem_V₀), hQ.z_ne_one, hchar, ?_, hquot, hwc⟩
  rw [hpCore]
  exact quasithin_isQ8D8 hQ.q8d8

theorem involutionClassCount_eq_two_of_eps_one (hGold : Asc76X.GoldschmidtTheoremA)
    (hGs : IsSimpleGroup G) (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P)
    (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') :
    CFSG.Quasithin.involutionClassCount G = 2 := by
  have hV₀2 : ∀ w ∈ V₀, w * w = 1 := fun w hw => h.mul_self (h.V₀_le hw)
  have hR2 : ∀ r ∈ R, r * r = 1 := fun r hr => h.mul_self (mem_sup_left hr)
  obtain ⟨z₀, hz₀, hz₀1, -⟩ := exists_ne_one_ne h.card_V₀ hV₀2 (one_mem V₀)
  obtain ⟨r₀, hr₀, hr₀1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  exact involutionClassCount_eq_two (by rw [sq]; exact hV₀2 z₀ hz₀) hz₀1
    (by rw [sq]; exact hR2 r₀ hr₀) hr₀1 (h.not_isConj_of_mem_R hz₀ hz₀1 hr₀ hr₀1)
    fun x hx2 hx1 => h.isConj_or_isConj hIIa hP hPC hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf
      hsup hV'inv hz₀ hz₀1 hr₀ hr₀1 hx2 hx1

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
