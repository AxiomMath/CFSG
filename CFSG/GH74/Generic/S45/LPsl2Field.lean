module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHilbert90
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsDihedral
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAction

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.AutL2Facts
open scoped MatrixGroups

theorem odd_sq_mod_eight {m : ℕ} (hm : Odd m) : (m * m) % 8 = 1 := by
  have h : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by
    obtain ⟨k, hk⟩ := hm
    omega
  rw [Nat.mul_mod]
  rcases h with h | h | h | h <;> rw [h]

theorem isSquare_two_of_fieldAut {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (σ : F ≃+* F) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) : IsSquare (2 : F) := by
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
  have hmod : Fintype.card F % 8 = 1 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact odd_sq_mod_eight (hpodd.pow)
  rw [FiniteField.isSquare_two_iff]
  omega


@[expose] def uSL {F : Type*} [Field F] (w : F) (hw : 2 * (w * w) = 1) : SL(2, F) :=
  ⟨!![w, w; -w, w], by
    rw [Matrix.det_fin_two_of]
    linear_combination hw⟩

@[expose] def negOneSL (F : Type*) [Field F] : SL(2, F) :=
  ⟨-1, by simp [Matrix.det_neg]⟩

@[simp] theorem uSL_coe {F : Type*} [Field F] {w : F} (hw : 2 * (w * w) = 1) :
    ((uSL w hw : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![w, w; -w, w] := rfl

@[simp] theorem negOneSL_coe (F : Type*) [Field F] :
    ((negOneSL F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := rfl

theorem negOneSL_mem_center (F : Type*) [Field F] : negOneSL F ∈ Subgroup.center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  ext i j
  by_cases h : i = j <;> simp [negOneSL, Matrix.scalar_apply, h]

theorem uSL_sq_coe {F : Type*} [Field F] {w : F} (hw : 2 * (w * w) = 1) :
    (((uSL w hw) ^ 2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
  simp only [uSL]
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> first | linear_combination hw | linear_combination -hw

theorem uSL_pow_four_mem_center {F : Type*} [Field F] {w : F} (hw : 2 * (w * w) = 1) :
    (uSL w hw) ^ 4 ∈ Subgroup.center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  ext i j
  have h4 : (uSL w hw) ^ 4 = (uSL w hw) ^ 2 * (uSL w hw) ^ 2 := by rw [← pow_add]
  rw [h4, Matrix.SpecialLinearGroup.coe_mul, uSL_sq_coe]
  rw [Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

theorem uSL_sq_not_mem_center {F : Type*} [Field F] {w : F} (hw : 2 * (w * w) = 1) :
    (uSL w hw) ^ 2 ∉ Subgroup.center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 1) hr
  simp only [uSL_sq_coe] at h01
  simp [Matrix.scalar_apply] at h01

theorem orderOf_mk_uSL {F : Type*} [Field F] {w : F} (hw : 2 * (w * w) = 1) :
    orderOf (QuotientGroup.mk (uSL w hw) : PSL2 F) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (QuotientGroup.mk (uSL w hw) : PSL2 F))
    (by
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact uSL_sq_not_mem_center hw)
    (by
      rw [show 2 ^ (1 + 1) = 4 by norm_num, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact uSL_pow_four_mem_center hw)
  rw [h]
  norm_num

theorem psl2FieldAut_mk_uSL {F : Type*} [Field F] {w : F} (hw : 2 * (w * w) = 1) (σ : F ≃+* F) :
    psl2FieldAut F σ (QuotientGroup.mk (uSL w hw)) = QuotientGroup.mk (uSL w hw) := by
  have h2 : (2 : F) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hw
    exact zero_ne_one hw
  have hσ : σ w * σ w = w * w := by
    have h1 : 2 * (σ w * σ w) = 1 := by
      have h2σ : σ (2 : F) = 2 := map_ofNat σ 2
      have := congrArg σ hw
      rwa [map_mul, map_mul, h2σ, map_one] at this
    apply mul_left_cancel₀ h2
    rw [h1, hw]
  have key : Matrix.SpecialLinearGroup.map σ.toRingHom (uSL w hw) = uSL w hw ∨
      Matrix.SpecialLinearGroup.map σ.toRingHom (uSL w hw) = negOneSL F * uSL w hw := by
    rcases mul_self_eq_mul_self_iff.1 hσ with h | h
    · left
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [h, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [h, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
          Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (uSL w hw)) = _
  rw [psl2RingEquiv_mk]
  rcases key with h | h
  · rw [h]
    rfl
  · rw [h]
    change QuotientGroup.mk (negOneSL F * uSL w hw) = QuotientGroup.mk (uSL w hw)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (negOneSL_mem_center F), one_mul]

theorem exists_fixed_order_four_of_field {F : Type} [Field F] [Finite F]
    (hK : IsOddPrimePower (Nat.card F)) (hF : ringChar F ≠ 2) (g : PGammaL2 F) (hg : orderOf g = 2)
    (hfield : g.right ≠ 1) :
    ∃ x : PSL2 F, semilinearAction F g x = x ∧ orderOf x = 4 := by
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
  obtain ⟨s, hs⟩ := isSquare_two_of_fieldAut hF σ hσ2 hfield
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply h2
    rw [hs]
    simp
  have hw : 2 * (s⁻¹ * s⁻¹) = 1 := by
    rw [hs]
    field_simp
  refine ⟨semilinearAction F (SemidirectProduct.inl C) (QuotientGroup.mk (uSL s⁻¹ hw)), ?_, ?_⟩
  · have hx₀ : semilinearAction F (SemidirectProduct.inr σ) (QuotientGroup.mk (uSL s⁻¹ hw)) =
        QuotientGroup.mk (uSL s⁻¹ hw) := by
      rw [semilinearAction_inr]
      exact psl2FieldAut_mk_uSL hw σ
    rw [hgC]
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self, hx₀]
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_mk_uSL hw

end CFSG.GH74.Generic.S45
