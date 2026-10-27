module

public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFive
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem D1L2Data.le_pCore_of_forall_le_centralizer {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _))
    (hodd : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p → barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) :=
  h.ph3.toTwoLocalPhaseThree.le_pCore_of_forall_le_centralizer h.ph3.isKGroup.1 h.ph3.ne_two
    h.normal_dichotomy h.isElemAbelian_barM h84 (hD2 G h.ph3.glob) hcomp hodd

theorem D1L2Data.exists_oddCore_not_centralized {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _))
    (hnorm : ¬ ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal) :
    ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ p ∧ ¬ barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
  by_contra hcon
  exact hnorm (stmtNormalSupOfLePCore h h84 hD2 (h.le_pCore_of_forall_le_centralizer h84 hD2
    hcomp fun s hs hs2 hsp => by_contra fun hns => hcon ⟨s, hs, hs2, hsp, hns⟩))

theorem gapR1bs_of (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) : GapR1bs := by
  intro G _ _ p _ P M H R Rbar hcfg _ K hK huniq _ hcent _ d hd e hcomp _ hnorm
  obtain ⟨n, hdn⟩ := hd
  have h := stmtL2Data G p P M H R Rbar hcfg K hK huniq hcent n d hdn e
  obtain ⟨s, hs, hs2, hsp, hns⟩ := h.exists_oddCore_not_centralized h84 hD2 hcomp hnorm
  exact h.false_of_oddCore_not_centralized h84 hD2 hs hs2 hsp hns

end CFSG.AGLEmbedding
