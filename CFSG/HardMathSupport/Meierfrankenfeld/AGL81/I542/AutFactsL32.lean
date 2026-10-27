module

public import CFSG.LieType.SteinbergBRAutGL32

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Matrix CFSG.QuasithinUnique.Setup.Family

theorem exists_det_one_conj_transpose_of_pow_seven :
    ∀ a b c d e f g h i : ZMod 2,
      ((!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 7 = 1) →
      ((!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1) →
      ∃ p q r s t u v w z : ZMod 2,
        (!![p, q, r; s, t, u; v, w, z] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 ∧
        (!![p, q, r; s, t, u; v, w, z] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 6 =
          ((!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 6).transpose *
            (!![p, q, r; s, t, u; v, w, z] : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  decide +kernel

theorem tau_conj_inv_of_orderOf_seven {x : GL32} (hx : orderOf x = 7) :
    ∃ k : GL32, CFSG.LieType.SteinbergBR.AutGL32.tau x = k * x⁻¹ * k⁻¹ := by
  have hx7 : x ^ 7 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have hX7 : (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx7, Units.val_one]
  have hX1 : (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h =>
    hx1 (Units.ext (by rw [h, Units.val_one]))
  have hinv : ((x⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 6 := by
    have : x⁻¹ = x ^ 6 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx7]
    rw [this, Units.val_pow_eq_pow_val]
  have h := exists_det_one_conj_transpose_of_pow_seven (x 0 0) (x 0 1) (x 0 2) (x 1 0) (x 1 1)
    (x 1 2) (x 2 0) (x 2 1) (x 2 2)
  rw [← Matrix.eta_fin_three (x : Matrix (Fin 3) (Fin 3) (ZMod 2))] at h
  obtain ⟨p, q, r, s, t, u, v, w, z, hdet, hK⟩ := h hX7 hX1
  set K : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![p, q, r; s, t, u; v, w, z] with hKdef
  have hKu : IsUnit K := (isUnit_iff_isUnit_det K).2 (by rw [hdet]; exact isUnit_one)
  refine ⟨hKu.unit, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, CFSG.LieType.SteinbergBR.AutGL32.tau_val, hinv]
  rw [Matrix.eta_fin_three (x : Matrix (Fin 3) (Fin 3) (ZMod 2))] at hK ⊢
  exact hK.symm

theorem mulAut_GL32_cases {x : GL32} (hx : orderOf x = 7) (σ : MulAut GL32) :
    (∃ g : GL32, σ = MulAut.conj g) ∨ ∃ k : GL32, σ x = k * x⁻¹ * k⁻¹ := by
  rcases aut_GL32_cases σ with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inl ⟨s, hs⟩
  · right
    obtain ⟨k, hk⟩ := tau_conj_inv_of_orderOf_seven hx
    refine ⟨s * k, ?_⟩
    rw [hs, MulAut.mul_apply, MulAut.conj_apply]
    have hk' : CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 (ZMod 2) x = k * x⁻¹ * k⁻¹ := hk
    rw [hk']
    group

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
