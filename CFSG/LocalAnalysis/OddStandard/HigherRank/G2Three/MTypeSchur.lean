module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Center

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open CFSG.ComponentClassification.HarrisLit

theorem isMTypeSchur_of_isSU43 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersOdd)
    {K : Type} [Group K] [Finite K] (hK : Group.IsPerfect K)
    (hB : IsSU43 (K ⧸ CFSG.oddCore K)) : IsMTypeSchur 3 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : CFSG.oddCore K = CFSG.pPrimeCore 2 K := by
    rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (CFSG.oddCore K)).ker := by
    rw [QuotientGroup.ker_mk', hcore]
    exact Nat.prime_two.coprime_iff_not_dvd.mp CFSG.pPrimeCore_coprime_card
  have hO : CFSG.pPrimeCore 2 (K ⧸ CFSG.oddCore K) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_piCore (K ⧸ CFSG.oddCore K) 2]
    let e : K ⧸ CFSG.oddCore K ≃* K ⧸ CFSG.pPrimeCore 2 K :=
      QuotientGroup.quotientMulEquivOfEq hcore
    have hmap := CFSG.LocalCores.piCore_map_mulEquiv ({q : Nat.Primes | q.val ≠ 2}) e
    have hbot : CFSG.piCore ({q : Nat.Primes | q.val ≠ 2}) (K ⧸ CFSG.pPrimeCore 2 K) = ⊥ := by
      rw [← CFSG.pPrimeCore_eq_piCore (K ⧸ CFSG.pPrimeCore 2 K) 2]
      exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp (by rw [hmap, hbot])
  refine Center47.isMTypeSchur_of_surjective' hGA (by norm_num : (3 : ℕ) ≠ 2)
    (QuotientGroup.mk' (CFSG.oddCore K)) (QuotientGroup.mk'_surjective _) hker hK hB.1 hO
    ⟨.PSU, 4, 1, hB.2.2.2⟩ ?_ ?_
  ·
    rw [hB.2.1]
    exact ⟨2, by norm_num⟩
  ·
    have hfac := factorization_card_griessHopfMultiplier_psu hGA
      (by norm_num : (3 : ℕ) ≠ 2) (by norm_num : (4 : ℕ) ≠ 0) (by norm_num : Even (4 : ℕ))
      hB.2.2.2
    have h4 : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.Prime.factorization_pow Nat.prime_two,
        Finsupp.single_eq_same]
    have hgcd : Nat.gcd 4 (3 ^ 1 + 1) = 4 := by norm_num
    rw [hfac, hgcd, hB.2.1, h4]

end CFSG.OddStandard.HigherRank.G2Three
