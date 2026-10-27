module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableL3Bound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TablePSL2p
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

section TwoPart

variable {F : Type} [Field F] [CharP F 2] [Finite F]

theorem k32_l3_card_two_part :
    ∃ m : ℕ, Odd m ∧ Nat.card (LinearFlag.projectiveSL 3 F) = Nat.card F ^ 3 * m := by
  obtain ⟨S, hS⟩ := LinearFlag.exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(LinearFlag.projUnitriangular 3 F).index, ?_, ?_⟩
  · have h := S.not_dvd_index
    rw [hS] at h
    exact Nat.odd_iff.mpr (by omega)
  · have h := (LinearFlag.projUnitriangular 3 F).card_mul_index
    rw [LinearFlag.card_projUnitriangular] at h
    simpa using h.symm

end TwoPart

theorem k32ExclPSL3_proved
    : K32ExclPSL3 := by
  intro K _ _ hq n hn hmodel hK
  by_cases h1 : n = 1
  · subst h1
    exact k32ExclPSL2p_proved K hq 7 ⟨by norm_num, Or.inr ⟨3, by norm_num, by norm_num⟩⟩
      (by norm_num) (Id2519.psl2_seven_of_psl3_two hmodel) hK
  · obtain ⟨-, F, hFfield, hFfin, hcard, ⟨e₀⟩⟩ := hmodel
    have hperf : Group.IsPerfect K := hq.1
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card, hcard])
    have e₁ : K ≃* StatedProj (StatedSL 3 F) := e₀
    let e : K ≃* LinearFlag.projectiveSL 3 F := e₁.trans (Id2519.projectiveSLEquivStatedProj 3 F).symm
    obtain ⟨m, hm, hmcard⟩ := k32_l3_card_two_part (F := F)
    have hfac := k32_two_pow_factorization (N := Nat.card (LinearFlag.projectiveSL 3 F)) (k := n * 3)
      (by rw [hmcard, hcard, ← pow_mul]) hm
    by_cases hn2 : n = 2
    · subst hn2
      have hF4 : Nat.card F = 4 := by rw [hcard]; norm_num
      refine k32_noDatum_of_iso2 hperf e k32_center_projectiveSL_three (k32ZBound2_l3_four hF4) ?_ ?_
      · rw [hfac]
        norm_num
      · rw [hfac]
        norm_num
    · have hn3 : 3 ≤ n := by omega
      refine k32_noDatum_of_iso2 hperf e k32_center_projectiveSL_three k32ZBound2_l3 ?_ ?_
      · rw [hfac, hcard]
        have h1 : 16 * 2 ^ n = 2 ^ (n + 4) := by rw [pow_add]; ring
        rw [h1]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      · rw [hfac, hcard]
        have h1 : 8 * 2 ^ n = 2 ^ (n + 3) := by rw [pow_add]; ring
        rw [h1]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end CFSG.QuasithinUnique.DoubleA3
