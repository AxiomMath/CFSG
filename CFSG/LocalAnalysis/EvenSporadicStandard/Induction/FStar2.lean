module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

theorem FStarSimple.eq_of_isComponent (hN : FStarSimple N) {M : Subgroup H}
    (hq : CFSG.IsQuasisimple ↥M) (hsub : M.IsSubnormal) : M = N := by
  have hMN : M ≤ N := by
    rw [← hN.generalizedFitting_eq]
    exact le_trans (le_sSup (show CFSG.IsComponent M from ⟨hq, hsub⟩)) le_sup_right
  have hsn : (M.subgroupOf N).IsSubnormal := hsub.subgroupOf
  have := hN.isSimpleGroup
  have hne : M.subgroupOf N ≠ ⊥ := by
    intro hb
    have hNt := CFSG.LocalCores.isQuasisimple_nontrivial hq
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥M)
    apply hx
    have hmem : (⟨(x : H), hMN x.2⟩ : ↥N) ∈ M.subgroupOf N := x.2
    rw [hb, Subgroup.mem_bot] at hmem
    have h1 : (x : H) = 1 := congrArg Subtype.val hmem
    exact Subtype.ext h1
  have htop : M.subgroupOf N = ⊤ := (hsn.eq_bot_or_top_of_isSimpleGroup ‹_›).resolve_left hne
  exact le_antisymm hMN (Subgroup.subgroupOf_eq_top.1 htop)

theorem FStarSimple.oddCore_eq_bot (hN : FStarSimple N) : CFSG.oddCore H = ⊥ := by
  have hNn := hN.normal
  have := hN.isSimpleGroup
  set O : Subgroup H := CFSG.oddCore H with hO
  have hodd : Odd (Nat.card O) := odd_card_oddCore' H
  have hOn : O.Normal := inferInstance
  have hNeven : ¬ Odd (Nat.card ↥N) := by
    intro hNodd
    have hsolv := CFSG.Milestones.odd_order_solvable hNodd
    obtain ⟨a, b, hab⟩ := hN.nonabelian
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  have hmeet : O ⊓ N = ⊥ := by
    haveI : (O.subgroupOf N).Normal := hOn.subgroupOf N
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.subgroupOf N) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact disjoint_iff.1 h
    · exfalso
      have hNO : N ≤ O := Subgroup.subgroupOf_eq_top.1 h
      exact hNeven (hodd.of_dvd_nat (Subgroup.card_dvd_of_le hNO))
  have hcomm : ⁅O, N⁆ = ⊥ := by
    apply le_bot_iff.1
    calc ⁅O, N⁆ ≤ O ⊓ N := Subgroup.commutator_le_inf O N
      _ = ⊥ := hmeet
  have hOC : O ≤ centralizer (N : Set H) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hON : O ≤ N := hOC.trans hN.centralizer_le
  rw [← hmeet]
  exact (inf_eq_left.2 hON).symm

end CFSG.EvenSporadicStandard.Induction
