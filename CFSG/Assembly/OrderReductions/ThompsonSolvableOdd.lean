module

public import CFSG.Assembly.OrderReductions.SolvableOddStability
public import CFSG.Assembly.OrderReductions.ThompsonQuotientCharacteristic

public section

namespace CFSG.OrderReductions.ThompsonSolvableOdd

open CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeComplementCore CFSG.OrderReductions.ThompsonCoreProduct
open CFSG.OrderReductions.ThompsonCenter

theorem thompsonCenter_characteristic_of_trivial_core {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (odd_order : Odd (Nat.card group)) (core_bot : primeComplementCore prime group = ⊥)
    (sylow : Sylow prime group) :
    ((thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype).Characteristic := by
  apply CFSG.OrderReductions.ThompsonCharacteristic.glauberman_characteristic prime odd_prime sylow
    (CFSG.OrderReductions.SolvablePrimeCore.centralizer_primeCore_le prime core_bot)
  intro normal normal_instance prime_normal
  exact CFSG.OrderReductions.SolvableOddStability.primeStable_of_solvable_odd prime prime_normal
    (conjugationAction normal) odd_order

theorem thompsonCenter_nontrivial_of_trivial_core {group : Type*} [Group group] [Finite group]
    [Nontrivial group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (core_bot : primeComplementCore prime group = ⊥) (sylow : Sylow prime group) :
    (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype ≠ ⊥ := by
  have nontrivial := coreProduct_nontrivial prime sylow
  simpa only [coreProduct, core_bot, bot_sup_eq] using nontrivial

theorem coreProduct_characteristic_of_solvable_odd {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (odd_order : Odd (Nat.card group)) (sylow : Sylow prime group) :
    (coreProduct prime sylow).Characteristic := by
  apply CFSG.OrderReductions.ThompsonQuotientCharacteristic.coreProduct_characteristic_of_quotient_stability
    prime odd_prime sylow
  intro normal normal_instance prime_normal
  exact CFSG.OrderReductions.SolvableOddStability.primeStable_of_solvable_odd prime prime_normal (conjugationAction normal)
    (odd_order.of_dvd_nat (Subgroup.card_quotient_dvd_card (primeComplementCore prime group)))

theorem coreProduct_independent_of_solvable_odd {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (odd_order : Odd (Nat.card group)) (sylow : Sylow prime group) :
    ∀ other : Sylow prime group, coreProduct prime other = coreProduct prime sylow :=
  independent_sylow_of_coreProduct_characteristic prime sylow
    (coreProduct_characteristic_of_solvable_odd prime odd_prime odd_order sylow)

end CFSG.OrderReductions.ThompsonSolvableOdd
