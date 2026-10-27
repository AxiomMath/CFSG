module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossAssembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamF4
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamG2
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamD4
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamTw
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerOne

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar

set_option linter.unusedSectionVars false

theorem eleven_le_of_prime_of_seven_le {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (h : p ≠ 7) :
    11 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem InnerPlaneBalanceAt.of_seven_of_ge_eleven {k : LieFamily} {e : ℕ}
    (h7 : InnerPlaneBalanceAtP k e fun p => p = 7)
    (h11 : InnerPlaneBalanceAtP k e fun p => 11 ≤ p) : InnerPlaneBalanceAt k e :=
  fun q hv p hp hp7 _ hpq he => by
    by_cases h : p = 7
    · exact h7 q hv p hp hp7 h hpq he
    · exact h11 q hv p hp hp7 (eleven_le_of_prime_of_seven_le hp hp7 h) hpq he

theorem localTwoBalanceCrossCharGtFive_of_inner_planes
    (hReeF4 : ReeF4InnerPlaneBalance)
    (hG2e2 : InnerPlaneBalanceAt .G2 2)
    (hD4e1 : InnerPlaneBalanceAt .trialityD4 1) (hD4e2 : InnerPlaneBalanceAt .trialityD4 2)
    (hD4e3 : InnerPlaneBalanceAt .trialityD4 3) (hD4e6 : InnerPlaneBalanceAt .trialityD4 6)
    (hF4e2 : InnerPlaneBalanceAt .F4 2) (hF4e3 : InnerPlaneBalanceAt .F4 3)
    (hF4e4 : InnerPlaneBalanceAt .F4 4) (hF4e6 : InnerPlaneBalanceAt .F4 6)
    (hE6e2 : InnerPlaneBalanceAt .E6 2) (hE6e3 : InnerPlaneBalanceAt .E6 3)
    (hE6e4 : InnerPlaneBalanceAt .E6 4) (hE6e6 : InnerPlaneBalanceAt .E6 6)
    (hTwe1 : InnerPlaneBalanceAt .twistedE6 1) (hTwe2 : InnerPlaneBalanceAt .twistedE6 2)
    (hTwe3 : InnerPlaneBalanceAt .twistedE6 3) (hTwe4 : InnerPlaneBalanceAt .twistedE6 4)
    (hTwe6 : InnerPlaneBalanceAt .twistedE6 6)
    (hE7e1 : InnerPlaneBalanceAtP .E7 1 fun p => p = 7) (hE7e2 : InnerPlaneBalanceAt .E7 2)
    (hE7e3 : InnerPlaneBalanceAt .E7 3) (hE7e4 : InnerPlaneBalanceAt .E7 4)
    (hE7e6 : InnerPlaneBalanceAt .E7 6)
    (hE8e1 : InnerPlaneBalanceAtP .E8 1 fun p => p = 7) (hE8e2 : InnerPlaneBalanceAt .E8 2)
    (hE8e3 : InnerPlaneBalanceAt .E8 3) (hE8e4 : InnerPlaneBalanceAt .E8 4)
    (hE8e5 : InnerPlaneBalanceAt .E8 5) (hE8e6 : InnerPlaneBalanceAt .E8 6)
    (hE8e8 : InnerPlaneBalanceAt .E8 8) (hE8e10 : InnerPlaneBalanceAt .E8 10)
    (hE8e12 : InnerPlaneBalanceAt .E8 12) :
    LocalTwoBalanceCrossCharGtFive := by
  refine localTwoBalanceCrossCharGtFive_of_exceptional hReeF4 fun k hk => ?_
  cases k with
  | G2 =>
    exact crossCharTwoFamCat_G2_of_classes innerPlaneBalanceAt_G2_one hG2e2
  | trialityD4 =>
    refine crossCharTwoFamCat_D4_of_classes fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> assumption
  | F4 =>
    refine crossCharTwoFamCat_F4_of_classes fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact innerPlaneBalanceAt_F4_one
    all_goals assumption
  | E6 =>
    refine crossCharTwoFamCat_E6_of_classes fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact innerPlaneBalanceAt_E6_one
    all_goals assumption
  | twistedE6 =>
    refine crossCharTwoFamCat_twistedE6_of_classes fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> assumption
  | E7 =>
    refine crossCharTwoFamCat_E7_of_classes fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact InnerPlaneBalanceAt.of_seven_of_ge_eleven hE7e1 innerPlaneBalanceAtP_E7_one
    all_goals assumption
  | E8 =>
    refine crossCharTwoFamCat_E8_of_classes fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact InnerPlaneBalanceAt.of_seven_of_ge_eleven hE8e1 innerPlaneBalanceAtP_E8_one
    all_goals assumption
  | A => exact hk.elim
  | twistedA => exact hk.elim
  | B => exact hk.elim
  | C => exact hk.elim
  | D => exact hk.elim
  | twistedD => exact hk.elim
  | suzuki => exact hk.elim
  | reeG2 => exact hk.elim
  | reeF4 => exact hk.elim
  | tits => exact hk.elim

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
