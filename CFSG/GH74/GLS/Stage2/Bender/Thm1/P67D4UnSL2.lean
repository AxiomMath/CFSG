module

public import CFSG.LieType.Steinberg.PartBRankOne

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.LieType.Steinberg Matrix

section SL2

variable {k : Type*} [Field k]

@[expose] def unSL2W : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] def unSL2Diag (t : kˣ) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![(t : k), 0; 0, ((t⁻¹ : kˣ) : k)], by simp [Matrix.det_fin_two]⟩

theorem coe_unSL2W : ((unSL2W : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
    !![0, 1; -1, 0] := rfl

theorem coe_unSL2Diag (t : kˣ) :
    ((unSL2Diag t : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(t : k), 0; 0, ((t⁻¹ : kˣ) : k)] := rfl

theorem un_sl2_adapted_eq {t s : k} (ht : t ≠ 0) (hts : t * s = 1) :
    sl2Lower (-t) * sl2Upper s = sl2Upper (-s) * unSL2W * unSL2Diag (Units.mk0 t ht) := by
  have hs : s = t⁻¹ := eq_inv_of_mul_eq_one_right hts
  subst hs
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Upper, coe_unSL2W,
    coe_unSL2Diag, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ht]

theorem un_sl2_conj_eq {t s : k} (hts : t * s = 1) (c : k) :
    sl2Lower (-t) * sl2Upper s * sl2Lower c * sl2Upper (-s) * sl2Lower t =
      sl2Upper (-(c * s ^ 2)) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Upper, Matrix.mul_fin_two]
  have ht : t ≠ 0 := left_ne_zero_of_mul_eq_one hts
  have hs : s = t⁻¹ := eq_inv_of_mul_eq_one_right hts
  subst hs
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

theorem un_sl2Upper_inv (a : k) : (sl2Upper a)⁻¹ = sl2Upper (-a) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem un_sl2Lower_inv (a : k) : (sl2Lower a)⁻¹ = sl2Lower (-a) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {G : Type*} [Group G]

theorem un_adapted_elt (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* G) (τ : G ≃* G)
    (ε : k ≃+* k) (κ' : k) (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (κ' * ε a)))
    {t : k} (ht : t ≠ 0) (hnorm : t * (κ' * ε t) = 1) :
    (ρ (sl2Lower t))⁻¹ * τ (ρ (sl2Lower t)) =
      ρ (sl2Upper (-(κ' * ε t))) * ρ unSL2W * ρ (unSL2Diag (Units.mk0 t ht)) := by
  rw [hl, ← map_inv, ← map_mul, ← map_mul, ← map_mul, un_sl2Lower_inv]
  exact congrArg ρ (un_sl2_adapted_eq ht hnorm)

theorem un_theta_upper (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* G) (τ : G ≃* G)
    (ε : k ≃+* k) (κ κ' : k) (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower (κ * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (κ' * ε a)))
    {t : k} (hnorm : t * (κ' * ε t) = 1) (a : k) :
    (ρ (sl2Lower t))⁻¹ * τ (ρ (sl2Lower t) * ρ (sl2Upper a) * (ρ (sl2Lower t))⁻¹) *
        ρ (sl2Lower t) = ρ (sl2Upper (-(κ * ε a * (κ' * ε t) ^ 2))) := by
  rw [map_mul, map_mul, map_inv, hu, hl, ← map_inv, ← map_inv, un_sl2Lower_inv,
    un_sl2Upper_inv]
  have key := un_sl2_conj_eq hnorm (κ * ε a)
  rw [← key]
  simp only [map_mul, mul_assoc]

end SL2

section SL2b

variable {k : Type*} [Field k]

theorem un_sl2Upper_add (a b : k) : sl2Upper (a + b) = sl2Upper a * sl2Upper b := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem un_sl2Lower_add (a b : k) : sl2Lower (a + b) = sl2Lower a * sl2Lower b := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem un_sl2W_diag (t : kˣ) : unSL2W * unSL2Diag t = unSL2Diag t⁻¹ * unSL2W := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unSL2W, coe_unSL2Diag, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem un_sl2Lower_eq {s : k} (hs : s ≠ 0) :
    sl2Lower s = sl2Upper s⁻¹ * unSL2W * unSL2Diag (-(Units.mk0 s hs)) * sl2Upper s⁻¹ := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Upper, coe_unSL2W,
    coe_unSL2Diag, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hs]

end SL2b

end CFSG.GH74.GLS.Stage2.Bender.Thm1
