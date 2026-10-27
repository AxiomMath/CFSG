module

public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCartanRank
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

theorem center_specialLinear_four_eq_bot (F : Type) [Field F] [Finite F] [CharP F 2] :
    Subgroup.center (SpecialLinearGroup (Fin 4) F) = ⊥ := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 4) F)) = 1 := by
    rw [Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 4) (R := F)).toEquiv]
    have hmax : max (Fintype.card (Fin 4)) 1 = 4 := by simp
    rw [hmax, CFSG.LieType.Steinberg.CentralExt.SLClosed.card_rootsOfUnity_eq_gcd (k := F) 4,
      Fintype.card_eq_nat_card]
    have hodd : Odd (Nat.card F - 1) := odd_card_sub_one_of_char_two
    have hcop : Nat.Coprime 4 (Nat.card F - 1) := by
      rw [show 4 = 2 ^ 2 by norm_num, Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
      exact (Nat.coprime_two_left).2 hodd
    exact Nat.coprime_iff_gcd_eq_one.1 hcop
  exact Subgroup.card_eq_one.1 hcard

end CFSG.ClassicalGroups.SpecialLinear

end
