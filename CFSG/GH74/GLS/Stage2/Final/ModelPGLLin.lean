module

public import CFSG.GH74.GLS.Stage2.Final.ModelPGLGen

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GorensteinWalter

variable {F : Type} [Field F]

theorem isSquare_or_neg [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F % 4 = 3) (x : Fˣ) :
    IsSquare x ∨ IsSquare (-x) := by
  have : Fintype F := Fintype.ofFinite F
  have hr : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2
  have hcard : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 4 * k + 3 := ⟨Nat.card F / 4, by omega⟩
  have hn : Fintype.card F / 2 = 2 * k + 1 := by omega
  rcases FiniteField.pow_dichotomy hr x.ne_zero with h | h
  · left
    rw [FiniteField.unit_isSquare_iff hr]
    apply Units.ext
    simpa using h
  · right
    rw [FiniteField.unit_isSquare_iff hr]
    apply Units.ext
    have hodd : Odd (Fintype.card F / 2) := ⟨k, by omega⟩
    rw [Units.val_pow_eq_pow_val, Units.val_neg, hodd.neg_pow, h, Units.val_one]
    simp

theorem lin_psi_range [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F % 4 = 3) :
    ((Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* PGL2 F).comp
      (Hpm (ModelData.lin F)).subtype).range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨g₀, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  have hδ : ((Matrix.GeneralLinearGroup.det g₀ : Fˣ) : F) = (g₀ : Matrix (Fin 2) (Fin 2) F).det :=
    Matrix.GeneralLinearGroup.val_det_apply g₀
  set δ := Matrix.GeneralLinearGroup.det g₀ with hδdef
  have key : ∀ (u : Fˣ) (ε : F), (ε = 1 ∨ ε = -1) → (u : F) * u = ε * ((δ⁻¹ : Fˣ) : F) →
      Matrix.ProjGenLinGroup.mk g₀ ∈ ((Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* PGL2 F).comp
        (Hpm (ModelData.lin F)).subtype).range := by
    intro u ε hε hu
    have hdet : ((sc2 u * g₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = ε := by
      rw [Units.val_mul, Matrix.det_mul, det_sc2, ← hδ]
      have h0 : ((δ : Fˣ) : F) ≠ 0 := Units.ne_zero _
      have : ((δ⁻¹ : Fˣ) : F) = ((δ : Fˣ) : F)⁻¹ := Units.val_inv_eq_inv_val δ
      rw [sq, hu, this]
      field_simp
    refine ⟨⟨sc2 u * g₀, Subgroup.mem_top _, by rw [hdet]; exact hε⟩, ?_⟩
    show Matrix.ProjGenLinGroup.mk (sc2 u * g₀) = Matrix.ProjGenLinGroup.mk g₀
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  rcases isSquare_or_neg h2 h4 δ⁻¹ with ⟨u, hu⟩ | ⟨u, hu⟩
  · refine key u 1 (Or.inl rfl) ?_
    have := congrArg (fun v : Fˣ => (v : F)) hu
    simpa using this.symm
  · refine key u (-1) (Or.inr rfl) ?_
    have := congrArg (fun v : Fˣ => (v : F)) hu
    simp only [Units.val_neg, Units.val_mul] at this
    linear_combination -this

theorem pglStmt_lin [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) (hq4 : Nat.card F % 4 = 3) :
    PglStmt (ModelData.lin F) (Nat.card F) (dP _ (dRefl F) (Subgroup.mem_top _)) :=
  pglStmt_of_surj (Subgroup.mem_top _)
    ⟨F, inferInstance, inferInstance,
      (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* PGL2 F).comp (Hpm (ModelData.lin F)).subtype, rfl,
      MonoidHom.range_eq_top.1 (lin_psi_range h2 hq4),
      fun g => mk_eq_one_iff_pm (clsFacts_lin h2 h5 hq4) g.2⟩

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
