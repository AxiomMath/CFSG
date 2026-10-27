module

public import CFSG.LieType.SeitzGeneration.OuterHeisWords

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F]

theorem transposeSL_inv (g : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.transpose g⁻¹ = (SpecialLinearGroup.transpose g)⁻¹ := by
  ext i j
  simp [← Matrix.adjugate_transpose]

theorem transposeSL_transposeSL (g : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g) = g := by
  ext i j
  simp

theorem transposeSL_mul (a b : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.transpose (a * b) =
      SpecialLinearGroup.transpose b * SpecialLinearGroup.transpose a := by
  ext i j
  simp [Matrix.mul_apply, mul_comm]

theorem transposeSL_one : SpecialLinearGroup.transpose (1 : SpecialLinearGroup (Fin 3) F) = 1 := by
  ext i j
  simp [Matrix.one_apply, eq_comm]

@[expose] def invTransposeSL : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F where
  toFun g := (SpecialLinearGroup.transpose g)⁻¹
  map_one' := by rw [transposeSL_one, inv_one]
  map_mul' a b := by rw [transposeSL_mul, _root_.mul_inv_rev]

theorem invTransposeSL_invTransposeSL (g : SpecialLinearGroup (Fin 3) F) :
    invTransposeSL (invTransposeSL g) = g := by
  show (SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g)⁻¹)⁻¹ = g
  rw [transposeSL_inv, transposeSL_transposeSL, inv_inv]

theorem invTransposeSL_coe (g : SpecialLinearGroup (Fin 3) F) :
    ((invTransposeSL g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      adjugate (g : Matrix (Fin 3) (Fin 3) F)ᵀ := by
  simp [invTransposeSL]

theorem invTransposeSL_shiftSL :
    invTransposeSL (shiftSL : SpecialLinearGroup (Fin 3) F) = shiftSL := by
  ext i j
  rw [invTransposeSL_coe]
  fin_cases i <;> fin_cases j <;>
    simp [shiftSL, adjugate_fin_three, Matrix.transpose_apply]

theorem invTransposeSL_diagSL (a b d : F) (h : a * b * d = 1) :
    invTransposeSL (diagSL a b d h) = diagSL (b * d) (a * d) (a * b)
      (by linear_combination (a * b * d + 1) * h) := by
  ext i j
  rw [invTransposeSL_coe]
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, adjugate_fin_three, Matrix.transpose_apply]

theorem invTranspose_conj_shift (c : F) (T₀ : SpecialLinearGroup (Fin 3) F)
    (hT₀ : (T₀ : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec ![1, 1, 1] ![3 * c, 0, -(3 * c)]) :
    ((invTransposeSL (shiftSL * T₀ * shiftSL⁻¹) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec ![1, -1, 0] ![3 * c, 3 * c, 3 * c] := by
  have hT : (T₀ : Matrix (Fin 3) (Fin 3) F) =
      !![1 + 3 * c, 0, -(3 * c); 3 * c, 1, -(3 * c); 3 * c, 0, 1 - 3 * c] := by
    rw [hT₀]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp
    all_goals ring
  have hS : ((shiftSL : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl
  have hSi : adjugate ((shiftSL : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
    rw [hS, adjugate_fin_three]
    simp
  have h1 : ((shiftSL * T₀ * shiftSL⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      !![1 - 3 * c, 3 * c, 0; -(3 * c), 1 + 3 * c, 0; -(3 * c), 3 * c, 1] := by
    have : ((shiftSL * T₀ * shiftSL⁻¹ : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
        ((shiftSL : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (T₀ : Matrix (Fin 3) (Fin 3) F) *
          adjugate ((shiftSL : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      simp
    rw [this, hT, hSi, hS]
    simp
  rw [invTransposeSL_coe, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjugate_fin_three, Matrix.transpose_apply] <;> ring

theorem outerHeisCore : OuterHeisCore := by
  intro F _ _ hF3 h4 ω α hω hω1 hα hαc
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h3 : (3 : F) ≠ 0 := by
    intro h
    apply hω1
    have h2 : (ω - 1) ^ 2 = 0 := by linear_combination hω - ω * h
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have hα1 : α - 1 ≠ 0 := fun h => hαc ⟨1, by linear_combination (-1 : F) * h⟩
  obtain ⟨b, hb0, hb3⟩ := exists_pow_three_ne_one h4
  have hα'1 : α * b ^ 3 - 1 ≠ 0 := by
    intro h
    apply hαc
    refine ⟨b⁻¹, ?_⟩
    field_simp
    linear_combination (-1 : F) * h
  have hb31 : b ^ 3 - 1 ≠ 0 := sub_ne_zero.2 hb3
  set K : Subgroup (SpecialLinearGroup (Fin 3) F) := Subgroup.closure (outerHeisSet ω α) with hKdef
  have hK : FixSL (heisC α) ⊆ K := fun k hk => Subgroup.subset_closure (Or.inl (Or.inl (Or.inl hk)))
  have hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K := by
    intro a b d h
    refine Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ?_)))
    apply mem_FixSL_of_mul_comm
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisD, diagSL, Matrix.mul_apply, Matrix.diagonal_apply] <;> ring
  have hshift : (shiftSL : SpecialLinearGroup (Fin 3) F) ∈ K := by
    have hD : heisD ω = !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [heisD]
    refine Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨ω, ?_⟩)))
    show heisD ω * !![0, 0, 1; 1, 0, 0; 0, 1, 0] = ω • (!![0, 0, 1; 1, 0, 0; 0, 1, 0] * heisD ω)
    rw [hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | ring1 | linear_combination (-1 : F) * hω3
  have hγ₁ : (-(ω + 2)) ^ 2 + 3 * (-(ω + 2)) + 3 = 0 := by linear_combination hω
  have hγ₂ : (-(ω ^ 2 + 2)) ^ 2 + 3 * (-(ω ^ 2 + 2)) + 3 = 0 := by
    linear_combination (ω ^ 2 - ω + 1) * hω
  have hsum : -(ω + 2) + -(ω ^ 2 + 2) = -3 := by linear_combination (-1 : F) * hω
  set c : F := 1 / (α - 1) - 1 / (α * b ^ 3 - 1) with hcdef
  have hc : c ≠ 0 := by
    have : c = α * (b ^ 3 - 1) / ((α - 1) * (α * b ^ 3 - 1)) := by
      rw [hcdef]; field_simp; ring
    rw [this]
    exact div_ne_zero (mul_ne_zero hα (hb31)) (mul_ne_zero hα1 hα'1)
  have htau : ∀ (γ : F) (hγ : γ ^ 2 + 3 * γ + 3 = 0), outerTauSL γ c ∈ K := by
    intro γ hγ
    have hs : (α - 1) * (γ / (α - 1)) = γ := by field_simp
    have hs' : (α * b ^ 3 - 1) * (γ / (α * b ^ 3 - 1)) = γ := by field_simp
    have hYs : outerYSL hγ (γ / (α - 1)) ∈ K :=
      hK (mem_FixSL_of_mul_comm (outerY_comm hs).symm)
    have hYs' : outerYSL hγ (γ / (α * b ^ 3 - 1)) ∈ K :=
      outerYSL_mem_of_conj hb0 hγ hK hdiag hs'
    have e : outerTauSL γ c =
        outerYSL hγ (γ / (α - 1)) * (outerYSL hγ (γ / (α * b ^ 3 - 1)))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      apply Subtype.ext
      have h1 : γ / (α - 1) = γ / (α * b ^ 3 - 1) + c * γ := by
        rw [hcdef]; field_simp; ring
      have h2 := outerY_eq_tau hγ (γ / (α * b ^ 3 - 1)) c
      rw [← h1] at h2
      exact h2.symm
    rw [e]
    exact K.mul_mem hYs (K.inv_mem hYs')
  have hT0 : outerTauSL (-(ω + 2)) c * outerTauSL (-(ω ^ 2 + 2)) c ∈ K :=
    K.mul_mem (htau _ hγ₁) (htau _ hγ₂)
  have hT0m : ((outerTauSL (-(ω + 2)) c * outerTauSL (-(ω ^ 2 + 2)) c :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec ![1, 1, 1] ![3 * c, 0, -(3 * c)] := outerTau_mul hsum c
  have hT1 : shiftSL * (outerTauSL (-(ω + 2)) c * outerTauSL (-(ω ^ 2 + 2)) c) * shiftSL⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem hshift hT0) (K.inv_mem hshift)
  set K' : Subgroup (SpecialLinearGroup (Fin 3) F) := K.comap invTransposeSL with hK'
  have hdiag' : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K' := by
    intro a b d h
    show invTransposeSL (diagSL a b d h) ∈ K
    rw [invTransposeSL_diagSL]
    exact hdiag _ _ _ _
  have hshift' : (shiftSL : SpecialLinearGroup (Fin 3) F) ∈ K' := by
    show invTransposeSL shiftSL ∈ K
    rw [invTransposeSL_shiftSL]
    exact hshift
  have hg'K' : invTransposeSL (shiftSL * (outerTauSL (-(ω + 2)) c * outerTauSL (-(ω ^ 2 + 2)) c) *
      shiftSL⁻¹) ∈ K' := by
    show invTransposeSL (invTransposeSL _) ∈ K
    rw [invTransposeSL_invTransposeSL]
    exact hT1
  have hg'm := invTranspose_conj_shift c _ hT0m
  have htop : K' = ⊤ := by
    refine eq_top_of_torus_shift_transvection hdiag' hshift' hb0 hb3 hg'm (by simp) (by simp)
      (by simp) ?_ hg'K'
    simp [h3, hc]
  rw [eq_top_iff]
  intro g _
  have hg : invTransposeSL g ∈ K' := htop ▸ Subgroup.mem_top _
  have hg2 : invTransposeSL (invTransposeSL g) ∈ K := hg
  rwa [invTransposeSL_invTransposeSL] at hg2

end CFSG.LieType.SeitzGeneration
