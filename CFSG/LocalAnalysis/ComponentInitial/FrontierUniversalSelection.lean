module

public import CFSG.LocalAnalysis.ComponentInitial.RankDominanceSelected
public import CFSG.LocalAnalysis.ComponentInitial.RankThreeUniversalComponent
public import CFSG.LocalAnalysis.ComponentInitial.ConstantSelectedFourGroup
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

namespace FrontierUniversalSelection

variable {G : Type} [Group G] [Finite G]

theorem pRank_eq_assembly_pRank (H : Subgroup G) :
    CFSG.pRank 2 H = CFSG.Assembly.pRank 2 H := CFSG.SectionRank.pRank_coe_eq_assemblyPRank 2 H

theorem rank_realization {J A : Subgroup G} (hAC : A ≤ centralizer (J : Set G))
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥)
    (hJA : ∀ b ∈ A, b ≠ 1 → CFSG.Assembly.IsComponentOf J (centralizer ({b} : Set G)))
    (hM3 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
      CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
      (center Q).index = (center J).index →
      (CFSG.pPrimeCore 2 Q).index = (CFSG.pPrimeCore 2 J).index →
      ∀ B : Subgroup G, B ≤ centralizer (Q : Set G) → CFSG.IsElementaryAbelian 2 B → t ∈ B →
        Nat.card B ≤ Nat.card A) :
    CFSG.pRank 2 (centralizer (J : Set G)) = CFSG.pRank 2 A := by
  rw [pRank_eq_assembly_pRank, pRank_eq_assembly_pRank]
  refine pRank_centralizer_eq_pRank hAC
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).1 hAe) hA1 hJA
    fun t ht hJt B hBC hBe htB => hM3 t ht J hJt (RankDominance.isTwoPComponent_of_isComponent
      ((isComponentOf_iff_isComponent_subgroupOf hJt.1).1 hJt)) rfl rfl B hBC
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 B).2 hBe) htB

theorem standard_or_universal_of_selected {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) (hK : CFSG.Assembly.KProper C G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {a : G} (ha : orderOf a = 2)
    {J : Subgroup G} (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)))
    (hJ2 : CFSG.Assembly.ComponentType.IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))))
    {A : Subgroup G} (hAC : A ≤ centralizer (J : Set G)) (hAe : CFSG.IsElementaryAbelian 2 A)
    (haA : a ∈ A) (hJr : 2 ≤ CFSG.pRank 2 J)
    (hJA : ∀ b ∈ A, b ≠ 1 → CFSG.Assembly.IsComponentOf J (centralizer ({b} : Set G)))
    (hM1 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
        (center Q).index ≤ (center J).index)
    (hM2 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
      CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
      (center Q).index = (center J).index →
        (CFSG.pPrimeCore 2 Q).index ≤ (CFSG.pPrimeCore 2 J).index)
    (hM3 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
      CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
      (center Q).index = (center J).index →
      (CFSG.pPrimeCore 2 Q).index = (CFSG.pPrimeCore 2 J).index →
      ∀ B : Subgroup G, B ≤ centralizer (Q : Set G) → CFSG.IsElementaryAbelian 2 B → t ∈ B →
        Nat.card B ≤ Nat.card A) :
    CFSG.Assembly.ComponentType.IsStandardSubgroup J ∨
      ∀ t ∈ centralizer (J : Set G), orderOf t = 2 →
        CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G)) := by
  have hA1 : A ≠ ⊥ := fun h => by
    have ha1 : a = 1 := (Subgroup.mem_bot).1 (h ▸ haA)
    rw [ha1, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have hdom := rank_dominance_propagates_selected_component hC hpump hK hB ha hJ hJ2 hAC hAe haA
    hM1 hM2 hM3
  rcases lt_or_ge (CFSG.pRank 2 J) (CFSG.pRank 2 A) with hrs | hrs
  ·
    right
    have hrank := rank_realization hAC hAe hA1 hJA hM3
    rw [pRank_eq_assembly_pRank, pRank_eq_assembly_pRank] at hrank
    have hA8 : 8 ≤ Nat.card A := by
      rw [RankDominance.card_eq_two_pow_pRank hAe]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact maximal_centralizer_rank_three_universal_component hC hpump hK hB hAC
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).1 hAe) hA8 hrank hJA hM1
  · rcases hrs.lt_or_eq with hlt | heq
    · exact Or.inl (hdom.2 hlt)
    · exact Or.inr (hdom.1 heq.le).1

end FrontierUniversalSelection

open FrontierUniversalSelection

theorem frontier_universal_selection {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper C G)
    (_hrank : 3 ≤ CFSG.Assembly.twoRank G) (hcomp : CFSG.Assembly.IsComponentType G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    (∃ t : G, orderOf t = 2 ∧ ∃ L : Subgroup G,
        CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧
          CFSG.Assembly.ComponentType.IsStandardSubgroup L) ∨
      (∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G,
        CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)) ∧ z ∈ J ∧
          ∃ r : ℕ, 3 ≤ r ∧ ∃ S : Sylow 2 J,
            Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) ∨
      ∃ a : G, orderOf a = 2 ∧ ∃ J : Subgroup G,
        CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)) ∧
        CFSG.Assembly.IsQuasisimple J ∧ 2 ≤ CFSG.pRank 2 J ∧
        Even (Nat.card (centralizer (J : Set G))) ∧
        ∀ t ∈ centralizer (J : Set G), orderOf t = 2 →
          CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G)) := by
  rcases initial_component_constant_on_selected_four_group_reduction_frontier hC hpump hK hcomp
    hB with h1 | h2 | ⟨a, ha, J, hJ, hJ2, A, hAC, hAe, haA, -, hJr, hJA, hmax, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  ·
    rw [← pRank_eq_assembly_pRank] at hJr
    have hAe' : CFSG.IsElementaryAbelian 2 A :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).2 hAe
    have hcore : ∀ Q : Subgroup G,
        (CFSG.Assembly.oddCore Q).index = (CFSG.pPrimeCore 2 Q).index := fun Q => by
      rw [CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    obtain ⟨hM1, hM2', hM3'⟩ := hmax
    have hM2 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
        CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
        CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
        (center Q).index = (center J).index →
          (CFSG.pPrimeCore 2 Q).index ≤ (CFSG.pPrimeCore 2 J).index := fun t ht Q hQ hQp hQd => by
      rw [← hcore, ← hcore]
      exact hM2' t ht Q hQ hQp hQd
    have hM3 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
        CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
        CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
        (center Q).index = (center J).index →
        (CFSG.pPrimeCore 2 Q).index = (CFSG.pPrimeCore 2 J).index →
        ∀ B : Subgroup G, B ≤ centralizer (Q : Set G) → CFSG.IsElementaryAbelian 2 B → t ∈ B →
          Nat.card B ≤ Nat.card A := fun t ht Q hQ hQp hQd hQe B hBC hBe htB =>
      hM3' t ht Q hQ hQp hQd (by rw [hcore, hcore]; exact hQe) B hBC
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 B).1 hBe) htB
    have heven : Even (Nat.card (centralizer (J : Set G))) := by
      have h := Subgroup.orderOf_dvd_natCard (centralizer (J : Set G)) (hAC haA)
      rw [ha] at h
      exact even_iff_two_dvd.2 h
    rcases standard_or_universal_of_selected hC hpump hK hB ha hJ hJ2 hAC hAe' haA hJr hJA hM1 hM2
      hM3 with hstd | huniv
    · exact Or.inl ⟨a, ha, J, hJ, hstd⟩
    · exact Or.inr (Or.inr ⟨a, ha, J, hJ, hJ.2.2, hJr, heven, huniv⟩)

end CFSG.LocalAnalysis.ComponentInitial
