module

public import CFSG.Open.GLADefs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts

open CFSG.Open

theorem isPGroup_center_of_glaPPrimeCore_eq_bot {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y]
    [Finite Y] (hO : GLAPPrimeCore p Y = ⊥) : IsPGroup p (Subgroup.center Y) := by
  have hO' : CFSG.pPrimeCore p Y = ⊥ := hO
  refine IsPGroup.of_card (n := (Nat.card (Subgroup.center Y)).primeFactorsList.length) ?_
  refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hr hrd => ?_
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hrd
  by_contra hrp
  have hN : (Subgroup.zpowers (z : Y)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 z.2)
  have hcard : Nat.card (Subgroup.zpowers (z : Y)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (z : Y))) := by
    rw [hcard]
    exact (Nat.coprime_primes hp hr).2 (Ne.symm hrp)
  have hbot := (CFSG.pPrimeCore_eq_bot_iff.mp hO') _ hN hcop
  rw [hbot, Subgroup.card_bot] at hcard
  exact hr.one_lt.ne hcard

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts

end
