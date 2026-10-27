module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActOdd
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActEven
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Skeleton

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup GorensteinWalter AutL2Facts

theorem L2Act.card_pgl2_eq_two_mul {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) : Nat.card (PGL2 F) = 2 * Nat.card (PSL2 F) := by
  rw [pgl2_card_formula, psl2_card_formula F hodd]
  have hq : Odd (Nat.card F) := by
    obtain ⟨p, n, -, hpodd, -, hc⟩ := hodd
    rw [hc]
    exact hpodd.pow
  have hdvd : 2 ∣ Nat.card F * (Nat.card F ^ 2 - 1) :=
    (Nat.Odd.sub_odd hq.pow odd_one).two_dvd.mul_left _
  exact (Nat.mul_div_cancel' hdvd).symm

theorem fritzL2Action : FritzL2Action := by
  intro X _ _ t L h F _ _ ⟨e⟩ T
  have hodd := L2Act.Config.isOddPrimePower h e
  obtain ⟨p, f, hp, hpodd, -, hF⟩ := id hodd
  have hp2 : p ≠ 2 := fun h2 => by
    rw [h2] at hpodd
    exact absurd hpodd (by decide)
  have h8 : (Nat.card (PSL2 F)).factorization 2 = 3 := by
    rw [← Nat.card_congr e.toEquiv]
    exact L2Act.Config.factorization_card_quot h
  rcases Nat.even_or_odd f with hfe | hfo
  · have hq4 : Nat.card F % 4 = 1 := by
      rw [hF]
      exact pow_mod_four_of_even hp hp2 hfe
    have hsq : IsSquare (-1 : F) := by
      classical
      have : Fintype F := Fintype.ofFinite F
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
      omega
    have h3 : twoVal F = 3 := by rw [← psl2_factorization_two hodd hq4, h8]
    exact L2Act.exists_l2Data_of_even h e hp hp2 hF hodd hsq hq4 h3 T
  · have hgal := eq_one_of_two_power_ringAut hp hF hfo
    have hcard : (Nat.card (PGL2 F)).factorization 2 = 4 := by
      rw [L2Act.card_pgl2_eq_two_mul hodd, Nat.factorization_mul (by norm_num) Nat.card_pos.ne',
        Finsupp.add_apply, h8, Nat.Prime.factorization_self Nat.prime_two]
    exact L2Act.exists_l2Data_of_odd h e hodd hgal hcard T

end CFSG.ComponentClassification.HSFLit
