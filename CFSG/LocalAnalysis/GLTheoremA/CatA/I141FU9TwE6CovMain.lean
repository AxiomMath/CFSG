module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9TwE6Abs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9TwE6CovLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9TwE6CovSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Main

set_option linter.unusedSectionVars false


theorem twE6CoverNoSU38_holds : TwE6CoverNoSU38 := by
  intro Q _ _ hQ hZ3 hQcat P _ _ hP hPZ hPcat ψ hψ z hz hψz
  by_contra hz1
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := twE6Cov_exists_statedSU hP hPZ hPcat
  letI : Field K := hKf
  haveI : Finite K := hKfin
  obtain ⟨u0, hu0c, hu01⟩ := twE6Cov_su38_cube hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardH : Nat.card (Subgroup.center ↥(CFSG.Open.StatedSU 3 8 K)) = 3 :=
    CFSG.Open.StatedCenterThree.card_center_statedSU_three hK (by norm_num)
  have hcardP : Nat.card (Subgroup.center P) = 3 := by
    rw [← hcardH]
    exact Nat.card_congr (Subgroup.centerCongr e).toEquiv
  set u : P := e.symm u0 with hu_def
  have hu3 : u ^ 3 = e.symm (u0 ^ 3) := by rw [hu_def, map_pow]
  have hu3c : u ^ 3 ∈ Subgroup.center P := by
    rw [hu3, Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.symm.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hu0c g']
  have hu31 : u ^ 3 ≠ 1 := by
    rw [hu3]
    intro h
    exact hu01 (e.symm.injective (by rw [h, map_one]))
  have hzg : Subgroup.zpowers (⟨z, hz⟩ : Subgroup.center P) = ⊤ :=
    zpowers_eq_top_of_prime_card (p := 3) hcardP
      (fun h => hz1 (by simpa using congrArg Subtype.val h))
  obtain ⟨k, hk⟩ : (⟨u ^ 3, hu3c⟩ : Subgroup.center P) ∈
      Subgroup.zpowers (⟨z, hz⟩ : Subgroup.center P) := by
    rw [hzg]
    exact Subgroup.mem_top _
  have hk' : z ^ k = u ^ 3 := by
    simpa using congrArg Subtype.val hk
  have hx3 : (ψ u) ^ 3 ∈ Subgroup.center Q := by
    rw [← map_pow, ← hk', map_zpow]
    exact Subgroup.zpow_mem _ hψz k
  have hx1 : (ψ u) ^ 3 = 1 := twE6Cov_central_cube hQ hZ3 hQcat hx3
  rw [← map_pow] at hx1
  exact hu31 (hψ (by rw [hx1, map_one]))

end Main

end CFSG.LocalAnalysis.GLTheoremA.I141F
