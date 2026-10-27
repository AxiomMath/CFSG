module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

theorem pComponent_centralizer_u1 [Finite K] (hodd : Odd (Nat.card K))
    {M : Subgroup (StatedProj (StatedSp 2 K))} (hMX : M ≤ centralizer {u1 K})
    (hM : CFSG.IsPComponent 2 (M.subgroupOf (centralizer {u1 K}))) :
    (M = E1 K ∨ M = E2 K) ∧ 5 ≤ Nat.card K := by
  have h2 := two_ne_zero_of_odd_card hodd
  have hperf := commutator_eq_of_isPComponent hMX hM
  have hne := ne_bot_of_isPComponent hM
  have hMX0 : M ≤ X0 K := perfect_le_map_centralizer (T1 K) hMX hperf
  have h3 : Nat.card K ≠ 3 := by
    intro h3
    have := isSolvable_X0_of_card_three h2 h3
    have hMs : Group.IsSolvable M :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hMX0)
        (Subgroup.inclusion_injective hMX0)
    have : Group.IsPerfect M := Subgroup.isPerfect_iff.mpr hperf
    have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hne
    exact Group.IsPerfect.not_isSolvable M hMs
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h5 : 5 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := hodd
    omega
  refine ⟨pComponent_eq_of_centralProduct X0_le_centralizer
    (fun c hc x hx => conj_mem_map_centralizer (T1 K) hc hx) (E1_le_X0 h2) (E2_le_X0 h2)
    (fun x hx e he => conj_mem_E1 h2 hx he) (fun x hx e he => conj_mem_E2 h2 hx he)
    (isQuasisimple_E1 h2 (by omega)) (isQuasisimple_E2 h2 (by omega))
    (fun x hx => exists_mul_of_mem_X0 h2 hx) (fun a ha b hb => commute_E1_E2 ha hb)
    (fun x hx hc => mem_E1_of_commute_E2 h2 hx hc) (fun x hx hc => mem_E2_of_commute_E1 h2 hx hc)
    (fun N hN hNp => perfect_le_map_centralizer (T1 K) hN hNp) hMX hM, h5⟩

end CFSG.ComponentClassification.CatFactsSp4
