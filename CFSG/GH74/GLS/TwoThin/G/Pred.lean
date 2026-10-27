module

public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup

abbrev GroupPred : Type 1 := (X : Type) → [Group X] → Prop

@[expose] def GroupPred.trivial : GroupPred := fun _ => True

@[expose] def Gen4Cen (H : Type) [Group H] : Prop :=
  Gen4 H ∧ ∃ c ∈ center H, orderOf c = 2

@[expose] def Gen4Comp (L : Type) [Group L] : Prop :=
  Gen4 L ∧ (SectionalTwoRankLE L 3 ∨ center L ≠ ⊥)

theorem Gen4Cen.gen4 {H : Type} [Group H] (h : Gen4Cen H) : Gen4 H := h.1

theorem Gen4Comp.gen4 {L : Type} [Group L] (h : Gen4Comp L) : Gen4 L := h.1

theorem gen4Comp_of_gen4Cen {H : Type} [Group H] [Finite H] (h : Gen4Cen H) (L : Subgroup H) :
    Gen4Comp ↥L := by
  obtain ⟨hg, c, hc, hc2⟩ := h
  refine ⟨Gen4.subgroup L hg, ?_⟩
  have hcc : ∀ x : H, x * c = c * x := Subgroup.mem_center_iff.mp hc
  have hcsq : c * c = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hc2)
  by_cases hcL : c ∈ L
  · right
    intro hbot
    have hmem : (⟨c, hcL⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcc g)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : c = 1 := congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hc2
    omega
  · left
    by_contra hcon
    exact CFSG.GH74.Generic.not_rankCertified_three_of_gen4 hg hcc hcsq hcL
      (CFSG.GH74.Generic.rankCertified_of_not_sectionalTwoRankLE hcon)

@[expose] noncomputable def RankThreePG : GroupPred :=
  fun G _ => CFSG.pRank 2 G ≤ 3

@[expose] noncomputable def RankThreeQ : GroupPred :=
  fun H _ => CFSG.pRank 2 H ≤ 3 ∧ ∃ c ∈ center H, orderOf c = 2

@[expose] noncomputable def RankThreeP : GroupPred :=
  fun L _ => CFSG.pRank 2 L ≤ 3 ∧ (center L = ⊥ → CFSG.pRank 2 L ≤ 2)

theorem RankThreePG.pRank_le {G : Type} [Group G] (h : RankThreePG G) : CFSG.pRank 2 G ≤ 3 := h

theorem RankThreeQ.pRank_le {H : Type} [Group H] (h : RankThreeQ H) : CFSG.pRank 2 H ≤ 3 := h.1

theorem RankThreeQ.exists_central_involution {H : Type} [Group H] (h : RankThreeQ H) :
    ∃ c ∈ center H, orderOf c = 2 := h.2

theorem RankThreeP.pRank_le {L : Type} [Group L] (h : RankThreeP L) : CFSG.pRank 2 L ≤ 3 := h.1

theorem RankThreeP.pRank_le_two_of_center_eq_bot {L : Type} [Group L] (h : RankThreeP L)
    (hz : center L = ⊥) : CFSG.pRank 2 L ≤ 2 := h.2 hz

end CFSG.GH74.GLS.TwoThin
