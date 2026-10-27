module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411L34M

public section

namespace CFSG.QuasithinUnique.Lin2.L34

open Matrix MatrixGroups

variable {F : Type} [Field F]

@[expose] def wSL (hF : F4 F) : SL(3, F) :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by
    rw [Matrix.det_fin_three]
    simp
    linear_combination (-1 : F) * hF.two⟩

@[expose] def invT (M : SL(3, F)) : SL(3, F) :=
  ⟨(M⁻¹.1)ᵀ, by rw [Matrix.det_transpose]; exact M⁻¹.2⟩

theorem invT_mul (M N : SL(3, F)) : invT (M * N) = invT M * invT N := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show ((M * N)⁻¹.1)ᵀ = (M⁻¹.1)ᵀ * (N⁻¹.1)ᵀ
  rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem invT_one : invT (1 : SL(3, F)) = 1 := by
  apply Subtype.ext
  show ((1 : SL(3, F))⁻¹.1)ᵀ = 1
  simp

@[expose] def dualHom (hF : F4 F) : SL(3, F) →* SL(3, F) where
  toFun M := wSL hF * invT M * (wSL hF)⁻¹
  map_one' := by simp [invT_one]
  map_mul' M N := by
    rw [invT_mul]
    group

theorem dualHom_apply (hF : F4 F) (M : SL(3, F)) :
    dualHom hF M = wSL hF * invT M * (wSL hF)⁻¹ := rfl

theorem dualHom_injective (hF : F4 F) : Function.Injective (dualHom hF) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  rw [dualHom_apply, mul_inv_eq_one, mul_eq_left] at hM
  have h1 : (M⁻¹.1)ᵀ = 1 := by
    have := congrArg Subtype.val hM
    simpa [invT] using this
  have h2 : M⁻¹.1 = 1 := Matrix.transpose_eq_one.1 h1
  have h3 : M⁻¹ = 1 := Subtype.ext h2
  simpa using h3

@[expose] noncomputable def dualEquiv [Finite F] (hF : F4 F) : SL(3, F) ≃* SL(3, F) :=
  MulEquiv.ofBijective (dualHom hF)
    ⟨dualHom_injective hF, Finite.injective_iff_surjective.1 (dualHom_injective hF)⟩

theorem dual_uT (hF : F4 F) (a b c : F) :
    dualHom hF (uT a b c) = uT (-b) (-a) (a * b - c) := by
  rw [dualHom_apply, mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have h := uT_inv a b c
  simp only [invT, h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSL, uT, Matrix.mul_apply, Fin.sum_univ_three]

theorem map_dual_Ys [Finite F] (hF : F4 F) :
    (Ys : Subgroup SL(3, F)).map (dualEquiv hF).toMonoidHom = Xs := by
  ext M
  constructor
  · rintro ⟨x, ⟨b, c, rfl⟩, rfl⟩
    refine ⟨-b, -c, ?_⟩
    show dualHom hF (uT 0 b c) = _
    rw [dual_uT]
    simp
  · rintro ⟨a, c, rfl⟩
    refine ⟨uT 0 (-a) (-c), ⟨-a, -c, rfl⟩, ?_⟩
    show dualHom hF (uT 0 (-a) (-c)) = _
    rw [dual_uT]
    simp

theorem dual_center [Finite F] (hF : F4 F) :
    Subgroup.map (dualEquiv hF).toMonoidHom (Subgroup.center SL(3, F)) =
      Subgroup.center SL(3, F) :=
  Subgroup.characteristic_iff_map_eq.1 inferInstance (dualEquiv hF)

@[expose] noncomputable def dualY [Finite F] (hF : F4 F) :
    (SL(3, F) ⧸ Subgroup.center SL(3, F)) ≃* (SL(3, F) ⧸ Subgroup.center SL(3, F)) :=
  QuotientGroup.congr (Subgroup.center SL(3, F)) (Subgroup.center SL(3, F)) (dualEquiv hF)
    (dual_center hF)

theorem normProps_Ys [Fintype F] (hcard : Fintype.card F = 4) :
    NormProps ((Ys : Subgroup SL(3, F)).map (QuotientGroup.mk' (Subgroup.center SL(3, F)))) := by
  have hF := F4.of_card hcard
  refine NormProps.of_map (dualY hF) ?_
  have hcomp : (dualY hF).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(3, F))) =
      (QuotientGroup.mk' (Subgroup.center SL(3, F))).comp (dualEquiv hF).toMonoidHom := by
    ext s
    exact QuotientGroup.congr_mk _ _ (dualEquiv hF) (dual_center hF) s
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_dual_Ys]
  exact normProps_Xs hcard

end CFSG.QuasithinUnique.Lin2.L34
