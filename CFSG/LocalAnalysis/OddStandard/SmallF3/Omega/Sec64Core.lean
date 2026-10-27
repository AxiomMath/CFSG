module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Eq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Ord8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64TIRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec64_core [Finite G] (hout : Asc82Outside) {T H : Subgroup G} {x y : G}
    (c : Sec64Cfg T H x y) (halt : Sec64Tri T H y) : Sec64Out T H y := by
  by_cases hTR : T ≤ centralizer ({y} : Set G)
  · exact sec64_case_eq c halt hTR
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let U : Subgroup G := T ⊓ centralizer ({y} : Set G) ⊓ H
    have hUT : U ≤ T := fun u hu => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hu).1).1
    have hpg : IsPGroup 2 ↥U := c.isPGroup.to_le hUT
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    have hyU : y ∈ U := c.mem_U
    have hdvd : 2 ∣ Nat.card ↥U := by
      have h := Subgroup.orderOf_dvd_natCard U hyU
      rwa [c.hy] at h
    have hn0 : n ≠ 0 := by
      intro h
      rw [h, pow_zero] at hn
      have : 2 ∣ 1 := hn ▸ hdvd
      omega
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn1 : n = 1 := by omega
      refine sec64_case_two hout c halt ?_ hTR
      have h2 : Nat.card ↥U = 2 := by rw [hn, hn1, pow_one]
      simpa [U] using h2
    · have h4 : 4 ≤ Nat.card ↥U := by
        rw [hn]
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      exact sec64_case_ti hout c halt (by simpa [U] using h4) hTR

end CFSG.OddStandard.SmallF3.Omega
