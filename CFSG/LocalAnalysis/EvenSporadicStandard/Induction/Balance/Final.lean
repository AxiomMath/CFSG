module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Alt
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Fi23.Simple

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem factorial_div_two_ne_ru : ∀ m : ℕ, 5 ≤ m → m.factorial / 2 ≠ 145926144000 := by
  intro m hm h
  rcases le_or_gt m 14 with h14 | h15
  · have h1 := Nat.factorial_le h14
    have h2 : Nat.factorial 14 = 87178291200 := by norm_num [Nat.factorial]
    omega
  · have h1 := Nat.factorial_le (show 15 ≤ m by omega)
    have h2 : Nat.factorial 15 = 1307674368000 := by norm_num [Nat.factorial]
    omega

theorem factorial_div_two_ne_fi23 :
    ∀ m : ℕ, 5 ≤ m → m.factorial / 2 ≠ 4089470473293004800 := by
  intro m hm h
  rcases le_or_gt m 20 with h20 | h21
  · have h1 := Nat.factorial_le h20
    have h2 : Nat.factorial 20 = 2432902008176640000 := by norm_num [Nat.factorial]
    omega
  · have h1 := Nat.factorial_le (show 21 ≤ m by omega)
    have h2 : Nat.factorial 21 = 51090942171709440000 := by norm_num [Nat.factorial]
    omega

theorem catalogNoRuFull_of_catalogNoRu (hC : CatalogNoRu) :
    CatalogNoRuFull := by
  intro H _ _ N hN hidx hcat M v hv hMC hM
  by_cases hAlt : IsAltType ↥N
  · exact false_of_isAlt hN hidx hAlt (s := .Ru) (c := 145926144000)
      CFSG.Sporadic.Ru.card_Ru (by norm_num) factorial_div_two_ne_ru hv hMC hM
  · exact hC H N hN hidx hcat hAlt M v hv hMC hM

theorem catalogFi23HostFull_of_catalogFi23Host
    (hC : CatalogFi23Host) : CatalogFi23HostFull := by
  intro H _ _ N hN hidx hcat L t ht2 hLC hL
  by_cases hAlt : IsAltType ↥N
  · exact (false_of_isAlt hN hidx hAlt (s := .Fi23) (c := 4089470473293004800)
      CFSG.Sporadic.Fi23.card_Fi23 (by norm_num) factorial_div_two_ne_fi23 ht2 hLC hL).elim
  · exact hC H N hN hidx hcat hAlt L t ht2 hLC hL

end CFSG.EvenSporadicStandard.Induction.Balance
