module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Census
public import Certificates.Certificate214034
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Classes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 CFSG.Perm
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
  CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Fi23Leaf

theorem l3Excl_Fi23_7_4 : L3Excl 4089470473293004800 7 4 :=
  l3Excl_of_check (B := 300) (by norm_num) (by norm_num) (by decide +kernel)

theorem noL3Eq_Fi23 : NoL3Eq 4089470473293004800 :=
  noL3Eq_of_check (B := 300) (by norm_num) (by decide +kernel)

section Main

theorem noL3Comp_J (x : CFSG.Sporadic.Fi23.J) (hx : orderOf x = 3) :
    NoL3Comp (Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J)) := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  obtain ⟨hpair, h1, h2, h3⟩ := Certificates.certificate214034
  have hcard : Nat.card ↥(⊤ : Subgroup J) = 4089470473293004800 := by
    rw [Subgroup.card_top, card_J]
  have hN : L3Excl (Nat.card ↥(⊤ : Subgroup J)) 7 4 := by
    rw [hcard]
    exact l3Excl_Fi23_7_4
  have hsub : ∀ c : Fin 4, c ≠ 0 → ¬ 7 ∣ Nat.card (Subgroup.centralizer ({t3 c} : Set J)) := by
    intro c hc
    fin_cases c
    · exact absurd rfl hc
    · exact h1
    · exact h2
    · exact h3
  obtain ⟨i, hi⟩ := fi23_three_classes x hx
  refine noL3Comp_centralizer_of_isConj hi.symm ?_
  by_cases h0 : i = 0
  · subst h0
    obtain ⟨a, ha, b, hb, hao, hbo, hd⟩ := hpair
    refine noL3Comp_of_prime_pair (P := ⊤) le_top (q := 7) (k := 4) (by norm_num) (by norm_num) hN
      ?_ ⟨a, ha, b, hb, hao, hbo, by simpa using hd⟩
    intro h72
    have h1 := h72.trans (Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({t3 0} : Set J)))
    rw [card_J] at h1
    norm_num at h1
  · exact noL3Comp_of_not_dvd_sub (P := ⊤) le_top (q := 7) (k := 4) (by norm_num) (by norm_num) hN
      (hsub i h0)

end Main

end Fi23Leaf

theorem sporL3DownInner_Fi23
    (hbr : SporadicBridges) : SporL3DownInner .Fi23 := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  have hM : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .Fi23).Group) :=
    ⟨fi23EquivJ.symm.trans (hbr .Fi23).some⟩
  have h1 := @sporL3DownInner_of_comp .Fi23 J inferInstance inferInstance hM
  have hcard : NoL3Eq (Nat.card J) := by
    rw [card_J]
    exact Fi23Leaf.noL3Eq_Fi23
  exact h1 hcard (fun x hx => Fi23Leaf.noL3Comp_J x hx)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
