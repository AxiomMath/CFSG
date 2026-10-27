module

public import CFSG.LieType.SteinbergBRUnitaryPlanePGL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoFieldData
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm

public noncomputable section

namespace CFSG.LieType

open Matrix CFSG.ComponentClassification.CatalogueBUnitaryTwo
  CFSG.ComponentClassification.CatalogueBLinearTwoDescent CFSG.LieType.Universal.Unitary
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry SteinbergBR
open scoped MatrixGroups

universe u v

variable {E : Type u} [Field E] [Finite E] {V : Type v} [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

theorem odd_unitary_plane_full_projective_linear_quotient (r f : ℕ) [Fact r.Prime]
    (hE : Nat.card E = (r ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation r f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 2) :
    let σ := unitaryFieldConjugation r f hE
    ∃ θ : isometryGroup h →* PGL(2, fixedSubfield E σ),
      Function.Surjective θ ∧
      (∀ g : isometryGroup h, θ g = 1 ↔
        ∃ c : Eˣ, (c : E) * σ c = 1 ∧ ∀ v, (g : V ≃ₗ[E] V) v = (c : E) • v) ∧
      (specialIsometry h).map θ =
        (SpecialLinearGroup.toPGL : SpecialLinearGroup (Fin 2) (fixedSubfield E σ) →*
          PGL(2, fixedSubfield E σ)).range ∧
      ∃ (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ)
        (e : specialIsometry h ≃* SpecialLinearGroup (Fin 2) (fixedSubfield E σ)),
        (∀ x y, h (B x) (B y) = hyperbolicForm σ x y) ∧ σ (t : E) = -(t : E) ∧
        (∀ g : specialIsometry h, (fixedSLMap σ (e g)).val = (diagonalGL t)⁻¹.val *
          LinearMap.toMatrix' ((B.trans g.val.val).trans B.symm).toLinearMap *
            (diagonalGL t).val) ∧
        ∀ g : specialIsometry h, θ g = SpecialLinearGroup.toPGL (e g) := by
  intro σ
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exfalso
      have h1 := Finite.one_lt_card (α := E)
      rw [hE, pow_zero, one_pow] at h1
      exact lt_irrefl 1 h1
    · exact hf
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f E :=
    ⟨Fact.out, hf, by rw [hE, ← pow_mul, mul_comm]⟩
  have hbar : ∀ x, hU.bar x = σ x := fun x => by
    rw [hU.bar_apply, unitaryFieldConjugation_apply]
  have h90 : ∀ u : E, σ u * u = 1 → ∃ c : E, c ≠ 0 ∧ σ c * u = c := by
    intro u hu
    have hn : hU.norm u = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm, hbar, mul_comm, hu]
    obtain ⟨c, hc0, hc⟩ := hU.exists_div_bar_eq hn
    refine ⟨c, hc0, ?_⟩
    have hbc : hU.bar c ≠ 0 := (hU.bar_eq_zero_iff).not.2 hc0
    rw [← hbar, ← hc, mul_div_cancel₀ _ hbc]
  have hnorm : ∀ a : E, σ a = a → ∃ c : E, c * σ c = a := by
    intro a ha
    have haF : a ∈ hU.fixedField := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_fixedField, hbar]
      exact ha
    obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨a, haF⟩
    refine ⟨c, ?_⟩
    have e := congrArg Subtype.val hc
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.coe_normHom,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm, hbar] at e
    exact e
  obtain ⟨-, B, t, e, hB, -, ht, he, -⟩ :=
    unitary_field_two_special_linear_isomorphism r f hE h hsym hnd hdim
  have ht0 : (t : E) ≠ 0 := t.ne_zero
  have hSU : ∀ g : specialIsometry h, thetaHom ht hB h90 g = SpecialLinearGroup.toPGL (e g) := by
    intro g
    refine thetaHom_apply_of_isRep ht hB h90 ⟨1, ?_⟩
    rw [Units.val_one, one_smul]
    change (diagonalGL t)⁻¹.val * LinearMap.toMatrix'
      ((B.trans g.val.val).trans B.symm).toLinearMap * (diagonalGL t).val = _
    rw [← he g]
    ext i j
    simp [fixedToE, fixedSLMap_entry]
  refine ⟨thetaHom ht hB h90, ?_, ?_, ?_, B, t, e, hB, ht, he, hSU⟩
  ·
    intro X
    induction X using ProjGenLinGroup.induction_on with
    | mk A₀ =>
      set M₀ : Matrix (Fin 2) (Fin 2) (fixedSubfield E σ) := A₀.val with hM₀
      have hfixd : ∀ i j, σ (M₀ i j : E) = (M₀ i j : E) := fun i j =>
        (mem_fixedSubfield E σ _).1 (M₀ i j).2
      set a : E := ((M₀.det : fixedSubfield E σ) : E) with ha
      have ha0 : a ≠ 0 := by
        rw [ha]
        exact fun h0 => Matrix.GeneralLinearGroup.det_ne_zero A₀ (Subtype.ext h0)
      have haσ : σ a⁻¹ = a⁻¹ := by
        rw [map_inv₀, ha, (mem_fixedSubfield E σ _).1 (M₀.det).2]
      obtain ⟨c, hc⟩ := hnorm a⁻¹ haσ
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hc
        exact inv_ne_zero ha0 hc.symm
      have hadet : a = (M₀ 0 0 : E) * M₀ 1 1 - (M₀ 0 1 : E) * M₀ 1 0 := by
        rw [ha, Matrix.det_fin_two]
        simp
      set M : Matrix (Fin 2) (Fin 2) E := c • !![(M₀ 0 0 : E), (M₀ 0 1 : E) * (t : E);
        (M₀ 1 0 : E) / (t : E), (M₀ 1 1 : E)] with hM
      have hiso : conjTr σ M * hyperbolicMatrix * M = hyperbolicMatrix := by
        refine isometry_of_fixed (hfixd 0 0) (hfixd 0 1) (hfixd 1 0) (hfixd 1 1) ht ?_
        rw [← hadet, hc, inv_mul_cancel₀ ha0]
      have hMdet : M.det ≠ 0 := by
        rw [hM, det_smul, Fintype.card_fin, Matrix.det_fin_two_of]
        refine mul_ne_zero (pow_ne_zero 2 hc0) ?_
        have e2 : (M₀ 0 0 : E) * M₀ 1 1 - (M₀ 0 1 : E) * t * (M₀ 1 0 / t) = a := by
          rw [hadet]
          field_simp
        rw [e2]
        exact ha0
      let L := M.toLinearEquiv' (Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hMdet))
      have hL : ∀ v, L v = M *ᵥ v := fun v => rfl
      let gV : V ≃ₗ[E] V := (B.symm.trans L).trans B
      have hgV : gV ∈ isometryGroup h := by
        intro x y
        change h (B (L (B.symm x))) (B (L (B.symm y))) = h x y
        rw [hB, hL, hL, (hyperbolic_isometry_iff_matrix σ M).2 hiso, ← hB,
          LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      have hcoord : coordMat B gV = M := by
        rw [coordMat, ← LinearMap.toMatrix'_toLin' M]
        congr 1
        refine LinearMap.ext fun x => ?_
        change B.symm (B (L (B.symm (B x)))) = _
        rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hL, Matrix.toLin'_apply]
      refine ⟨⟨gV, hgV⟩, thetaHom_apply_of_isRep ht hB h90 ⟨Units.mk0 c hc0, ?_⟩⟩
      change conjCoord B t gV = _
      rw [conjCoord_eq, hcoord, Units.val_mk0]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjugatedMatrix, hM, fixedToE, ← hM₀] <;> field_simp
  ·
    intro g
    constructor
    · intro hg1
      obtain ⟨A₀, hA₀⟩ := exists_isRep ht (coordMat_isometry hB g.2) h90
      have hmk : ProjGenLinGroup.mk A₀ = 1 := by
        rw [← thetaHom_apply_of_isRep ht hB h90 hA₀]
        exact hg1
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hmk
      obtain ⟨u, rfl⟩ := hmk
      obtain ⟨c, hc⟩ := hA₀
      have hlam0 : (c : E) * (u : fixedSubfield E σ) ≠ 0 :=
        mul_ne_zero c.ne_zero (fun h0 => u.ne_zero (Subtype.ext h0))
      set lam : Eˣ := Units.mk0 ((c : E) * (u : fixedSubfield E σ)) hlam0 with hlam
      have hconj : conjCoord B t g = (lam : E) • 1 := by
        rw [hc, hlam, Units.val_mk0]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [fixedToE]
      have hcoord : coordMat B g = (lam : E) • 1 := by
        have hD : (diagonalGL t).val * (diagonalGL t)⁻¹.val = 1 := (diagonalGL t).val_inv
        have hD' : (diagonalGL t)⁻¹.val * (diagonalGL t).val = 1 := (diagonalGL t).inv_val
        calc coordMat B g = (diagonalGL t).val * conjCoord B t g * (diagonalGL t)⁻¹.val := by
              rw [conjCoord, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hD, Matrix.one_mul,
                Matrix.mul_assoc, hD, Matrix.mul_one]
          _ = (lam : E) • 1 := by
              rw [hconj, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hD]
      have hv : ∀ v, (g : V ≃ₗ[E] V) v = (lam : E) • v := by
        intro v
        have e1 := coordMat_mulVec B g (B.symm v)
        rw [hcoord, LinearEquiv.apply_symm_apply, Matrix.smul_mulVec, Matrix.one_mulVec] at e1
        rw [← LinearEquiv.apply_symm_apply B ((g : V ≃ₗ[E] V) v), ← e1, map_smul,
          LinearEquiv.apply_symm_apply]
      refine ⟨lam, ?_, hv⟩
      have e1 := g.2 (B (Pi.single 0 1)) (B (Pi.single 1 1))
      rw [hv, hv, LinearMap.map_smulₛₗ₂, map_smul, hB, hyperbolicForm_apply] at e1
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne' (show (0 : Fin 2) ≠ 1 by decide),
        Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), map_one, map_zero, mul_one,
        mul_zero, add_zero, smul_eq_mul, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at e1
      rw [mul_comm]
      exact e1
    · rintro ⟨c, -, hc⟩
      refine (thetaHom_apply_of_isRep ht hB h90 (A₀ := 1) ⟨c, ?_⟩).trans ProjGenLinGroup.mk_one
      rw [conjCoord, coordMat_eq_smul hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Units.inv_mul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fixedToE]
  ·
    ext X
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨e ⟨g, hg⟩, (hSU ⟨g, hg⟩).symm⟩
    · rintro ⟨N, rfl⟩
      refine ⟨(e.symm N : isometryGroup h), (e.symm N).2, ?_⟩
      change thetaHom ht hB h90 (e.symm N) = _
      rw [hSU (e.symm N), e.apply_symm_apply]

end CFSG.LieType
