module

public import CFSG.LieType.OutStructureSecondBranchLinear
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneKSCenter
public import CFSG.LieType.OutStructureSevenOneEightField

public section

namespace CFSG.LieType.OutStructure

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_centralizer_pElement_not_mem_of_pRank_le_two
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hX2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hdvd : p ∣ Nat.card (Subgroup.centralizer (L : Set X))) :
    ∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p ∧ c ∉ L := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hcord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (L : Set X))) p hdvd
  refine ⟨(c : X), c.2, (Subgroup.orderOf_coe c).trans hcord, ?_⟩
  intro hcL
  have hcmem : (⟨(c : X), hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2 (y : X) y.2)
  have hdvdZ : p ∣ Nat.card (Subgroup.center ↥L) := by
    have hz : orderOf (⟨⟨(c : X), hcL⟩, hcmem⟩ : Subgroup.center ↥L) = p := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hcord]
    have h := orderOf_dvd_natCard (⟨⟨(c : X), hcL⟩, hcmem⟩ : Subgroup.center ↥L)
    rwa [hz] at h
  have h3 := CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactCenterRankFive_holds
    X hK L hL p hp hp5 hdvdZ
  have hmono : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  omega

theorem two_le_pRank_of_not_isPClosedMod
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hnot : ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
      (L ⊔ Subgroup.centralizer (L : Set X))) :
    2 ≤ CFSG.Open.pRank p L := by
  by_contra h
  have h1 : CFSG.Open.pRank p L ≤ 1 := by omega
  exact hnot (sevenOneThree_pClosed_of_pRank_le_one hK hp hp2 hL hLn h1)

theorem sevenOneThree_rankLeTwo_p5_of_maximalTorus
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp5 : 5 ≤ p) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hX2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hInput : ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)) →
      (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) ∨
      ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X) ∧
        ∃ E : Subgroup X, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧
          Nat.card E = p ^ CFSG.Open.pRank p L ∧ ∀ a ∈ E, a * x = x * a) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
      (L ⊔ Subgroup.centralizer (L : Set X)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnot
  rcases hInput hnot with ⟨c, hcC, hcord⟩ | ⟨x, hxord, hxU, E, hEL, hE, hEmax, hEc⟩
  ·
    have hCdvd : p ∣ Nat.card (Subgroup.centralizer (L : Set X)) := by
      have hc : orderOf (⟨c, hcC⟩ : ↥(Subgroup.centralizer (L : Set X))) = p := by
        rw [Subgroup.orderOf_mk, hcord]
      have h := orderOf_dvd_natCard (⟨c, hcC⟩ : ↥(Subgroup.centralizer (L : Set X)))
      rwa [hc] at h
    obtain ⟨c', hc'C, hc'ord, hc'L⟩ :=
      exists_centralizer_pElement_not_mem_of_pRank_le_two hK hp hp5 hL hLn hX2 hCdvd
    have hL2 : 2 ≤ CFSG.Open.pRank p L :=
      two_le_pRank_of_not_isPClosedMod hK hp hp2 hL hLn hnot
    obtain ⟨F, hFL, hF, hFcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2) hL2
    have h3 := three_le_pRank_of_linear_dichotomy hp hFL hF hFcard
      (Or.inl ⟨c', hc'C, hc'ord, hc'L⟩)
    omega
  ·
    have hxL : x ∉ L := fun hx => hxU (Subgroup.mem_sup_left hx)
    have hL2 : 2 ≤ CFSG.Open.pRank p L :=
      two_le_pRank_of_not_isPClosedMod hK hp hp2 hL hLn hnot
    have h3 := three_le_pRank_of_field_action_centralizes_maximal hp hxord hxL
      hEL hE hEmax hEc hL2
    omega

theorem sevenOneThree_holds_of_maximalTorus
    (hInput : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
      ∀ p : ℕ, p.Prime → p ≠ 2 → 5 ≤ p →
      ∀ L : Subgroup X, L.Normal → CFSG.IsComponent L →
      CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 →
      ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
          (L ⊔ Subgroup.centralizer (L : Set X)) →
        (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) ∨
        ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X) ∧
          ∃ E : Subgroup X, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧
            Nat.card E = p ^ CFSG.Open.pRank p L ∧ ∀ a ∈ E, a * x = x * a)
    (hThird : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
      ∀ p : ℕ, p.Prime → p ≠ 2 → 5 ≤ p →
      ∀ L : Subgroup X, L.Normal → CFSG.IsComponent L →
      CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 →
        CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
          (L ⊔ Subgroup.centralizer (L : Set X))) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneThree := by
  refine CFSG.LieType.OutStructureFull.sevenOneThree_holds_of ?_ hThird
  intro X _ _ hK p hp hp2 hp5 L hLn hL hX2
  exact sevenOneThree_rankLeTwo_p5_of_maximalTorus hK hp hp2 hp5 hL hLn hX2
    (hInput X hK p hp hp2 hp5 L hLn hL hX2)

end CFSG.LieType.OutStructure
