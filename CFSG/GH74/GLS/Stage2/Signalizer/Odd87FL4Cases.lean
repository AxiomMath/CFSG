module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4Block
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.P34Embed
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def Surv4 {F : Type} [Field F] (α : MulAut (projectiveSL 4 F)) : Prop :=
  (∃ B : GL (Fin 4) F, B * B = 1 ∧ Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2 ∧
      α = conjAut 4 F B) ∨
    (∃ (A : GL (Fin 4) F) (c : Fˣ), A * A = GeneralLinearGroup.scalar (Fin 4) c ∧
      ¬ IsSquare (c : F) ∧ α = conjAut 4 F A) ∨
    (∃ A : GL (Fin 4) F, α = conjAut 4 F A * dualAut 4 F ∧
      ((A : Matrix (Fin 4) (Fin 4) F)ᵀ = A ∨ (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A))

theorem linear4_involution_cases {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (hfodd : Odd f) (hK2 : ringChar F ≠ 2)
    (α : MulAut (projectiveSL 4 F)) (hα : α ^ 2 = 1) :
    (∃ ρ : SpecialLinearGroup (Fin 3) F →* projectiveSL 4 F, Function.Injective ρ ∧
      ∀ g, α (ρ g) = ρ g) ∨ Surv4 α := by
  classical
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := 4) (by norm_num)).2 α
  rw [hαeq] at hα ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 4 F), mul_one] at hα ⊢
      have h1 : conjAut 4 F (A * A) * fieldAut 4 F 1 = 1 := by
        rw [map_one, mul_one, map_mul, ← sq, hα]
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1
      by_cases hsq : IsSquare (c : F)
      · obtain ⟨μ, hμ⟩ := hsq
        have hμ0 : μ ≠ 0 := by
          rintro rfl
          rw [zero_mul] at hμ
          exact c.ne_zero hμ
        set B' : GL (Fin 4) F :=
          GeneralLinearGroup.scalar (Fin 4) (Units.mk0 μ hμ0)⁻¹ * A with hB'
        have hcB : conjAut 4 F B' = conjAut 4 F A := by
          rw [hB', map_mul, conjAut_scalar, one_mul]
        have hs : (Units.mk0 μ hμ0)⁻¹ * (Units.mk0 μ hμ0)⁻¹ * c = 1 := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_one]
          rw [hμ]
          field_simp
        have hBB : B' * B' = 1 := by
          calc B' * B' = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 μ hμ0)⁻¹ *
                GeneralLinearGroup.scalar (Fin 4) (Units.mk0 μ hμ0)⁻¹ * (A * A) := by
                rw [hB', mul_assoc, ← mul_assoc A, ← GeneralLinearGroup.scalar_commute]
                group
            _ = 1 := by rw [← hc, ← map_mul, ← map_mul, hs, map_one]
        have hBm : (B' : Matrix (Fin 4) (Fin 4) F) * B' = 1 := by
          rw [← Units.val_mul, hBB, Units.val_one]
        have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspaces hK2 hBm)
        rw [Module.finrank_fin_fun] at hsum
        by_cases h3 : 3 ≤ Module.finrank F (LinearMap.ker (toLin' B'.val - 1))
        · obtain ⟨ρ, hinj, hfix⟩ := exists_fixed_sl3_block_of_sq_gen (m := 1) le_rfl hK2 B' hBB h3
          exact Or.inl ⟨ρ, hinj, fun g => by rw [← hcB]; exact hfix g⟩
        · by_cases h3' : 3 ≤ Module.finrank F (LinearMap.ker (toLin' B'.val + 1))
          · have hker : LinearMap.ker (toLin' ((-B' : GL (Fin 4) F).val) - 1) =
                LinearMap.ker (toLin' B'.val + 1) := by
              ext v
              simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
                Module.End.one_apply, Units.val_neg, neg_mulVec]
              rw [← neg_add', neg_eq_zero]
            obtain ⟨ρ, hinj, hfix⟩ := exists_fixed_sl3_block_of_sq_gen (m := 1) le_rfl hK2 (-B')
              (by rw [neg_mul_neg, hBB]) (by rw [hker]; exact h3')
            exact Or.inl ⟨ρ, hinj, fun g => by rw [← hcB, ← conjAut_neg]; exact hfix g⟩
          · exact Or.inr (Or.inl ⟨B', hBB, by omega, hcB.symm⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨A, c, hc.symm, hsq, rfl⟩))
    · exact absurd hfodd (Nat.not_odd_iff_even.2
        (linear_field_involution_descent hp hf hcard (by norm_num) A σ hσ hα).1)
  · rw [pow_one] at hα ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 4 F), mul_one] at hα ⊢
      rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hα with hA | hA
      · exact Or.inr (Or.inr (Or.inr ⟨A, rfl, Or.inl hA⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨A, rfl, Or.inr hA⟩))
    · exact absurd hfodd (Nat.not_odd_iff_even.2
        (odd_linear_graph_field_involution_conjugacy hp hf hcard (by norm_num) A σ hσ hα).1)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
