module

public import CFSG.GH74.Generic.S45.LPsl2Field

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompL2Field

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.AutL2Facts CFSG.GH74.Generic.S45
open scoped MatrixGroups

@[expose] def dSL {F : Type*} [Field F] (i : F) (hi : i * i = -1) : SL(2, F) :=
  ⟨!![i, 0; 0, -i], by
    rw [Matrix.det_fin_two_of]
    linear_combination -hi⟩

@[simp] theorem dSL_coe {F : Type*} [Field F] {i : F} (hi : i * i = -1) :
    ((dSL i hi : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![i, 0; 0, -i] := rfl

theorem dSL_sq {F : Type*} [Field F] {i : F} (hi : i * i = -1) :
    dSL i hi * dSL i hi = negOneSL F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp only [dSL_coe, negOneSL_coe]
  rw [Matrix.mul_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> linear_combination hi

theorem uSL_mul_dSL_mul_uSL {F : Type*} [Field F] {i w : F} (hi : i * i = -1) (hw : 2 * (w * w) = 1) :
    uSL w hw * dSL i hi * uSL w hw = dSL i hi := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [uSL_coe, dSL_coe]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;>
    first | linear_combination i * hw | linear_combination -i * hw

theorem mk_dSL_conj {F : Type*} [Field F] {i w : F} (hi : i * i = -1) (hw : 2 * (w * w) = 1) :
    (QuotientGroup.mk (dSL i hi) : PSL2 F) * QuotientGroup.mk (uSL w hw) *
      (QuotientGroup.mk (dSL i hi) : PSL2 F)⁻¹ = (QuotientGroup.mk (uSL w hw) : PSL2 F)⁻¹ := by
  have hx : (QuotientGroup.mk (uSL w hw) : PSL2 F) * QuotientGroup.mk (dSL i hi) *
      QuotientGroup.mk (uSL w hw) = QuotientGroup.mk (dSL i hi) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, uSL_mul_dSL_mul_uSL]
  have hzx : (QuotientGroup.mk (dSL i hi) : PSL2 F) * QuotientGroup.mk (uSL w hw) =
      (QuotientGroup.mk (uSL w hw) : PSL2 F)⁻¹ * QuotientGroup.mk (dSL i hi) := by
    calc (QuotientGroup.mk (dSL i hi) : PSL2 F) * QuotientGroup.mk (uSL w hw)
        = (QuotientGroup.mk (uSL w hw) : PSL2 F)⁻¹ * (QuotientGroup.mk (uSL w hw) *
            QuotientGroup.mk (dSL i hi) * QuotientGroup.mk (uSL w hw)) := by group
      _ = _ := by rw [hx]
  rw [hzx, mul_assoc, mul_inv_cancel, mul_one]

theorem mk_dSL_sq {F : Type*} [Field F] {i : F} (hi : i * i = -1) :
    (QuotientGroup.mk (dSL i hi) : PSL2 F) * QuotientGroup.mk (dSL i hi) = 1 := by
  rw [← QuotientGroup.mk_mul, dSL_sq, QuotientGroup.eq_one_iff]
  exact negOneSL_mem_center F


theorem psl2FieldAut_mk_dSL {F : Type*} [Field F] {i : F} (hi : i * i = -1) (σ : F ≃+* F) :
    psl2FieldAut F σ (QuotientGroup.mk (dSL i hi)) = QuotientGroup.mk (dSL i hi) := by
  have hσ : σ i * σ i = i * i := by
    have := congrArg σ hi
    rwa [map_mul, map_neg, map_one, ← hi] at this
  have key : Matrix.SpecialLinearGroup.map σ.toRingHom (dSL i hi) = dSL i hi ∨
      Matrix.SpecialLinearGroup.map σ.toRingHom (dSL i hi) = negOneSL F * dSL i hi := by
    rcases mul_self_eq_mul_self_iff.1 hσ with h | h
    · left
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [h, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    · right
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [h, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
          Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (dSL i hi)) = _
  rw [psl2RingEquiv_mk]
  rcases key with h | h
  · rw [h]
    rfl
  · rw [h]
    change QuotientGroup.mk (negOneSL F * dSL i hi) = QuotientGroup.mk (dSL i hi)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (negOneSL_mem_center F), one_mul]


theorem card_mod_eight_of_fieldAut {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (σ : F ≃+* F) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) : Nat.card F % 8 = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  set p := ringChar F with hpdef
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := ringChar.charP F
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  let e : (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) := {
    toFun := fun sigma =>
      AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h :
            (sigma.toRingHom.comp (algebraMap (ZMod p) F) :
              ZMod p →+* F) = algebraMap (ZMod p) F :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }
  have hcardaut : Nat.card (F ≃+* F) = Module.finrank (ZMod p) F := by
    rw [Nat.card_congr e.toEquiv]
    exact IsGalois.card_aut_eq_finrank (ZMod p) F
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hdvd : 2 ∣ Module.finrank (ZMod p) F := by
    rw [← hcardaut, ← hord]
    exact orderOf_dvd_natCard σ
  obtain ⟨k, hk⟩ := hdvd
  have hcard : Nat.card F = (p ^ k) * (p ^ k) := by
    rw [← FiniteField.pow_finrank_eq_natCard p F, hk, two_mul, pow_add]
  have hpodd : Odd p := hp.odd_of_ne_two hF
  rw [hcard]
  exact odd_sq_mod_eight (hpodd.pow)


theorem exists_fixed_D8_of_field {F : Type} [Field F] [Finite F]
    (hK : IsOddPrimePower (Nat.card F)) (hF : ringChar F ≠ 2) (g : PGammaL2 F) (hg : orderOf g = 2)
    (hfield : g.right ≠ 1) :
    ∃ x z : PSL2 F, semilinearAction F g x = x ∧ semilinearAction F g z = z ∧ orderOf x = 4 ∧
      z * z = 1 ∧ z * x * z⁻¹ = x⁻¹ := by
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hK g hg hfield
  have hg2 : g * g = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg, pow_two] at h
    exact h
  obtain ⟨σ, hσ⟩ : ∃ σ : F ≃+* F, σ = g.right := ⟨_, rfl⟩
  rw [← hσ] at hC hfield
  have hgC : g = SemidirectProduct.inl C * SemidirectProduct.inr σ * (SemidirectProduct.inl C)⁻¹ := by
    rw [← hC]
    group
  have hσ2 : σ * σ = 1 := by
    have h1 : (SemidirectProduct.inr σ : PGammaL2 F) * SemidirectProduct.inr σ = 1 := by
      rw [← hC]
      calc (SemidirectProduct.inl C)⁻¹ * g * SemidirectProduct.inl C *
            ((SemidirectProduct.inl C)⁻¹ * g * SemidirectProduct.inl C)
          = (SemidirectProduct.inl C)⁻¹ * (g * g) * SemidirectProduct.inl C := by group
        _ = 1 := by rw [hg2]; group
    have hinj : Function.Injective (SemidirectProduct.inr : (F ≃+* F) → PGammaL2 F) :=
      SemidirectProduct.inr_injective
    apply hinj
    rw [map_mul, h1, map_one]
  have : Fintype F := Fintype.ofFinite F
  have h8 : Fintype.card F % 8 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_mod_eight_of_fieldAut hF σ hσ2 hfield
  obtain ⟨s, hs⟩ : IsSquare (2 : F) := FiniteField.isSquare_two_iff.2 ⟨by omega, by omega⟩
  obtain ⟨i, hi'⟩ : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.2 (by omega)
  have hi : i * i = -1 := hi'.symm
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply h2
    rw [hs]
    simp
  have hw : 2 * (s⁻¹ * s⁻¹) = 1 := by
    rw [hs]
    field_simp
  refine ⟨semilinearAction F (SemidirectProduct.inl C) (QuotientGroup.mk (uSL s⁻¹ hw)),
    semilinearAction F (SemidirectProduct.inl C) (QuotientGroup.mk (dSL i hi)), ?_, ?_, ?_, ?_, ?_⟩
  · have hx₀ : semilinearAction F (SemidirectProduct.inr σ) (QuotientGroup.mk (uSL s⁻¹ hw)) =
        QuotientGroup.mk (uSL s⁻¹ hw) := by
      rw [semilinearAction_inr]
      exact psl2FieldAut_mk_uSL hw σ
    rw [hgC]
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self, hx₀]
  · have hx₀ : semilinearAction F (SemidirectProduct.inr σ) (QuotientGroup.mk (dSL i hi)) =
        QuotientGroup.mk (dSL i hi) := by
      rw [semilinearAction_inr]
      exact psl2FieldAut_mk_dSL hi σ
    rw [hgC]
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self, hx₀]
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_mk_uSL hw
  · rw [← map_mul]
    rw [mk_dSL_sq hi, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact mk_dSL_conj hi hw

end CFSG.GH74.Generic.BProg.B3.L2CompL2Field
