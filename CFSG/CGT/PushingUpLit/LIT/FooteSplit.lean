module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.Assembly

theorem natCard_specialLinearGroup_two {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem isQuasisimple_top_of_natSL {L : Type} [Group L] [Finite L] (hL : IsShortGroup L) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule L n) :
    CFSG.IsQuasisimple (L ⧸ pCore 2 L) := by
  rcases hL.quotient_type with hq | hp
  · exact hq
  · exfalso
    obtain ⟨φ, -⟩ := hnat
    have hcard : Nat.card (L ⧸ pCore 2 L) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      Nat.card_congr φ.toEquiv
    rw [hcard, natCard_specialLinearGroup_two, GaloisField.card 2 n (by omega)] at hp
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    exact Nat.not_prime_mul (by omega) (by omega) hp

end CFSG.CGT.PushingUpLit
