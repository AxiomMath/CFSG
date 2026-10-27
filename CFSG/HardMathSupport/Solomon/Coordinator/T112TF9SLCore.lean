module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.RankThree.PartOne.OutStructure

variable {F : Type} [Field F] [Finite F]

theorem exists_conj_fieldAut_of_pow_three (α : MulAut (projectiveSL 3 F)) (h3 : α ^ 3 = 1)
    (hα : α ∉ linearAutGroup 3 F) :
    ∃ (M : GL (Fin 3) F) (σ : F ≃+* F),
      α = conjAut 3 F M * fieldAut 3 F σ * (conjAut 3 F M)⁻¹ := by
  have : Finite (MulAut (projectiveSL 3 F)) := finite_mulAut_projectiveSL 3
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := 3) (K := F)
  have hαE : α ∈ semilinearAutGroup 3 F := by
    have hidx' : (semilinearAutGroup 3 F).index ≤ 2 := by
      have h2 : (semilinearAutGroup 3 F).relIndex (standardAutGroup 3 F) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2
    refine mem_of_pow_mem_of_index_le_two _ hidx' (N := 3) (by decide) ?_
    rw [h3]
    exact (semilinearAutGroup 3 F).one_mem
  obtain ⟨B, τ, rfl⟩ := mem_semilinearAutGroup_iff.1 hαE
  have h1 := conjAut_mul_fieldAut_pow τ B 3
  rw [h3] at h1
  obtain ⟨hτ3, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) le_rfl _ _ h1.symm
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply hα
    rw [map_one, mul_one]
    exact conjAut_mem_linearAutGroup B
  have hτo : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
  obtain ⟨H, d, hH⟩ := CFSG.StandardType.OrdPRest.exists_hilbert90 (n := 3) (by norm_num) hτo B
    (c := c) hc.symm
  exact ⟨H, τ, CFSG.StandardType.OrdPRest.conjAut_mul_fieldAut_eq_conj' B H τ d hH⟩

open CFSG.HardMathSupport.Timmesfeld.LinearRank in
theorem exists_not_mem_linearAutGroup (hF : Nat.card F % 9 = 1)
    (H : Subgroup (MulAut (projectiveSL 3 F))) (hH : CFSG.Open.IsElemAbelian 3 H)
    (h27 : Nat.card H = 27) : ∃ α ∈ H, α ∉ linearAutGroup 3 F := by
  by_contra hcon
  push Not at hcon
  have hpK : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units]; omega
  let ρ : ↥(⊤ : Subgroup (GL (Fin 3) F)) →* MulAut (projectiveSL 3 F) :=
    (conjAut 3 F).comp (⊤ : Subgroup (GL (Fin 3) F)).subtype
  have hker : ∀ A : ↥(⊤ : Subgroup (GL (Fin 3) F)), ρ A = 1 ↔
      (A : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
    intro A
    rw [mem_center_iff]
    exact conjAut_eq_one_iff le_rfl _
  have hHρ : H ≤ ρ.range := by
    intro α hα
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hcon α hα)
    exact ⟨⟨A, trivial⟩, hA⟩
  have := card_le_of_scalar_kernel Nat.prime_three (by norm_num) hpK (by norm_num) _ ρ hker H hHρ hH
  rw [h27] at this
  norm_num at this

end CFSG.HardMathSupport.Solomon.Coordinator
