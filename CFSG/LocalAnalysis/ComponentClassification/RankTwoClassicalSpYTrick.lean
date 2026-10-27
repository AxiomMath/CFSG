module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalLevi

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

variable (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include h32 h4 h34

theorem not_le_normalizer_of_noNormalTwo {Y : Subgroup G} (hYA : Y ≤ A)
    (hTY : T ≤ centralizer (Y : Set G))
    (hNN : NoNormalTwo (rightConjugate A g ⊓ centralizer (Y : Set G))) :
    ¬ centralizer (Y : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G) := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRY : R ≤ centralizer (Y : Set G) := hc.sylowR.le.trans (centralizer_le hYA)
  have hAgT : rightConjugate A g ≤ centralizer (T : Set G) := by
    rw [le_centralizer_iff, centralizer_rightConjugate]
    exact hc.sylowT.le
  have hQle : (R ⊔ T) ⊓ rightConjugate A g ≤ rightConjugate A g ⊓ centralizer (Y : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (sup_le hRY hTY))
  have hQN : rightConjugate A g ⊓ centralizer (Y : Set G) ≤
      normalizer (((R ⊔ T) ⊓ rightConjugate A g : Subgroup G) : Set G) := by
    intro c hc'
    obtain ⟨hcA, hcY⟩ := mem_inf.mp hc'
    have hcT := hAgT hcA
    have hcR : c ∈ normalizer (R : Set G) := hle (mem_inf.mpr ⟨hcY, hcT⟩)
    exact mem_normalizer_inf (mem_normalizer_sup hcR (centralizer_le_normalizer _ hcT))
      (Subgroup.le_normalizer hcA)
  have hQbot := hNN _ hQle (hc.isPGroup_sup.to_le inf_le_left) hQN
  have hRTA : R ≤ T ⊔ rightConjugate A g := by
    have h := (rightConjugate_le_rightConjugate_iff (x := g)).mpr (hc.swap.le_sup h32 h4 h34)
    rwa [rightConjugate_sup, rightConjugate_inv_rightConjugate,
      rightConjugate_inv_rightConjugate] at h
  obtain ⟨r, hr, hr1⟩ := R.bot_or_exists_ne_one.resolve_left hc.R_ne_bot
  have hTA : T ≤ normalizer (rightConjugate A g : Set G) :=
    le_centralizer_iff.mp hAgT |>.trans (centralizer_le_normalizer _)
  have hr' : r ∈ ((T ⊔ rightConjugate A g : Subgroup G) : Set G) := hRTA hr
  rw [coe_mul_of_left_le_normalizer_right T _ hTA] at hr'
  obtain ⟨t, ht, a, ha, hra⟩ := hr'
  have hra' : t * a = r := hra
  have haQ : a ∈ (R ⊔ T) ⊓ rightConjugate A g := by
    refine mem_inf.mpr ⟨?_, ha⟩
    have : a = t⁻¹ * r := by rw [← hra']; group
    rw [this]
    exact mul_mem (mem_sup_right (inv_mem ht)) (mem_sup_left hr)
  rw [hQbot, mem_bot] at haQ
  rw [haQ, mul_one] at hra'
  rw [← hra'] at hr hr1
  have : t ∈ R ⊓ T := mem_inf.mpr ⟨hr, ht⟩
  rw [hc.inf_eq_bot, mem_bot] at this
  exact hr1 this

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
