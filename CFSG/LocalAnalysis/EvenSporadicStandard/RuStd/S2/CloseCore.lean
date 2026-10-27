module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Foundations.Basic

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.oddCore X ≤ CFSG.pPrimeCore 2 X :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have hdvd : Nat.card (CFSG.oddCore X) ∣ Nat.card (CFSG.pPrimeCore 2 X) :=
    Subgroup.card_dvd_of_le hle
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2) (G := X)))

theorem oddCore_quotient_eq_bot (X : Type*) [Group X] [Finite X] :
    CFSG.oddCore (X ⧸ CFSG.oddCore X) = ⊥ := by
  rw [CFSG.oddCore_eq_piCore (X ⧸ CFSG.oddCore X)]
  let e := QuotientGroup.quotientMulEquivOfEq (CFSG.oddCore_eq_piCore X)
  apply (Subgroup.map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [CFSG.LocalCores.piCore_map_mulEquiv]
  exact CFSG.LocalCores.prime_set_core_quotient {q : Nat.Primes | q.val ≠ 2}

theorem orderOf_mk_oddCore_eq_two {X : Type*} [Group X] [Finite X] {t : X} (ht : orderOf t = 2) :
    orderOf (QuotientGroup.mk t : X ⧸ CFSG.oddCore X) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, ht2, QuotientGroup.mk_one]
  · intro h
    have hdvd := Subgroup.orderOf_dvd_natCard _ ((QuotientGroup.eq_one_iff t).1 h)
    rw [ht] at hdvd
    exact (Nat.not_even_iff_odd.2 (odd_card_oddCore X)) (even_iff_two_dvd.2 hdvd)

end CFSG.EvenSporadicStandard.RuStd.S2.Close
