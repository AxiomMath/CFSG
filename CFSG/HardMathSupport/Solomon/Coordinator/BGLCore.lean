module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreStep5
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreStep4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix

theorem sl3SubfieldJoin_holds : SL3SubfieldJoin := by
  intro F _ _ σ h3 h hnr
  change ⊤ ≤ joinH σ h
  set u := (h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 with hu
  by_cases hind : ∀ b : Fin 3 → F, IsRat σ b → b ⬝ᵥ u = 0 → b = 0
  · exact top_le_joinH_of_indep h3 hind
  push Not at hind
  obtain ⟨b, hb, hbu, hb0⟩ := hind
  by_cases hrat : ∃ c : F, c ≠ 0 ∧ IsRat σ (c • u)
  swap
  · exact top_le_joinH_of_line (orderOf_prime_of_three h3) hb hb0 hbu hrat
  obtain ⟨c, hc0, hcu⟩ := hrat
  have hu0 : u ≠ 0 := by
    intro h0
    have : ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = Pi.single 0 1 := by
      rw [hu, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at this
    have := congrFun this 0
    simp at this
  have ha0 : c • u ≠ 0 := smul_ne_zero hc0 hu0
  obtain ⟨m, hm, hcol⟩ := exists_ratGL_col0 hcu ha0
  set cu : Fˣ := Units.mk0 c hc0
  set h₂ := Matrix.GeneralLinearGroup.scalar (Fin 3) cu * (m⁻¹ * h)
  have hsc : ∀ M : Matrix (Fin 3) (Fin 3) F,
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) cu : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * M = c • M := by
    intro M
    ext i j
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul,
      Units.val_mk0, cu, Matrix.smul_apply, smul_eq_mul]
  have hh₂ : (h₂ : Matrix (Fin 3) (Fin 3) F) =
      c • (((m⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * h) := by
    rw [show (h₂ : Matrix (Fin 3) (Fin 3) F) =
        ((Matrix.GeneralLinearGroup.scalar (Fin 3) cu : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) * ((m⁻¹ * h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        from Units.val_mul _ _, hsc, Units.val_mul]
  have hfix : (h₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [hh₂, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← hu, ← Matrix.mulVec_smul,
      ← hcol, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]
  have hnr₂ : NotRatProj σ h₂ := by
    rintro ⟨d, hd0, hd⟩
    apply hnr
    refine ⟨d * c, mul_ne_zero hd0 hc0, ?_⟩
    have hrat : IsRatM σ ((d * c) • (((m⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * h)) := by
      intro i j
      have := hd i j
      rw [hh₂] at this
      simpa [Matrix.smul_apply, mul_assoc] using this
    have hprod := IsRatM.mul (mem_ratGL.mp hm) hrat
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, coe_mul_inv, Matrix.one_mul] at hprod
    intro i j
    simpa [Matrix.smul_apply] using hprod i j
  have htop : ⊤ ≤ joinH σ (Matrix.GeneralLinearGroup.scalar (Fin 3) cu * (m⁻¹ * h)) :=
    top_le_joinH_of_fix (orderOf_prime_of_three h3) hfix hnr₂
  rw [joinH_scalar_mul] at htop
  exact top_le_joinH_of_rat_mul ((ratGL σ).inv_mem hm) htop

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
