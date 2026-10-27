module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableSp4Outer

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem k32ExclPSp4_proved : K32ExclPSp4 := by
  intro K _ _ hq n hn hmodel _
  obtain ⟨-, F, hFfield, hFfin, hcard, ⟨e₀⟩⟩ := hmodel
  have e : K ≃* StatedProj (StatedSp 2 F) := e₀
  have hperf : Group.IsPerfect K := hq.1
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  obtain ⟨m, hm, hmcard⟩ :=
    CFSG.ComponentClassification.SymmetricLocal.card_statedSp_eq_two_pow_mul_odd
      (r := 2) (k := F) hcard (by omega) (by norm_num)
  have hPcard : Nat.card (StatedProj (StatedSp 2 F)) = 2 ^ (n * 2 ^ 2) * m := by
    rw [← hmcard]
    exact Nat.card_congr (projSpEquiv F).toEquiv.symm
  have hfac := k32_two_pow_factorization hPcard hm
  refine k32_noDatum_of_iso2 hperf e k32_center_sp4 k32ZBound2_sp4 ?_ ?_
  · rw [hfac, hcard]
    have h1 : 16 * 2 ^ n = 2 ^ (n + 4) := by rw [pow_add]; ring
    rw [h1]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rw [hfac, hcard]
    have h1 : 8 * (2 ^ n) ^ 2 = 2 ^ (n * 2 + 3) := by rw [← pow_mul, pow_add]; ring
    rw [h1]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end CFSG.QuasithinUnique.DoubleA3
