module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.LieType.SpecialLinear

open Matrix

section Cocycle

variable {F : Type*} [Field F] {n : ℕ}

theorem apply_apply_eq_of_mul_self_eq_one {σ : F ≃+* F} (hσ : σ * σ = 1) (x : F) :
    σ (σ x) = x := by
  have h := DFunLike.congr_fun hσ x
  simpa [pow_two] using h

theorem mul_self_eq_one_of_trans_self_eq_refl {σ : F ≃+* F}
    (h : σ.trans σ = RingEquiv.refl F) : σ * σ = 1 := by
  ext x
  have hx := congrArg (fun e : F ≃+* F => e x) h
  simpa [RingEquiv.trans_apply, RingAut.mul_apply] using hx

theorem map_eq_of_mul_map_eq_scalar {σ : F ≃+* F} (hσ : σ.trans σ = RingEquiv.refl F)
    (hn : 1 ≤ n)
    {b : GL (Fin n) F} {lam : F} (hlam : lam ≠ 0)
    (hb : b * Matrix.GeneralLinearGroup.map σ.toRingHom b =
      Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 lam hlam)) :
    σ lam = lam := by
  classical
  have hσσx := apply_apply_eq_of_mul_self_eq_one (F := F)
    (mul_self_eq_one_of_trans_self_eq_refl hσ)
  let S : Fˣ →* GL (Fin n) F := Matrix.GeneralLinearGroup.scalar (Fin n)
  have hmapmap : Matrix.GeneralLinearGroup.map σ.toRingHom
      (Matrix.GeneralLinearGroup.map σ.toRingHom b) = b := by
    ext i j
    simp [hσσx]
  have hb_inv : Matrix.GeneralLinearGroup.map σ.toRingHom b =
      S (Units.mk0 lam hlam) * b⁻¹ := by
    calc Matrix.GeneralLinearGroup.map σ.toRingHom b
        = b⁻¹ * (b * Matrix.GeneralLinearGroup.map σ.toRingHom b) := by group
      _ = b⁻¹ * S (Units.mk0 lam hlam) := by rw [hb, show S (Units.mk0 lam hlam) =
            Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 lam hlam) from rfl]
      _ = S (Units.mk0 lam hlam) * b⁻¹ :=
          (Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 lam hlam) b⁻¹).symm
  have h1 := congrArg (Matrix.GeneralLinearGroup.map σ.toRingHom) hb
  rw [map_mul, Matrix.GeneralLinearGroup.map_scalar] at h1
  rw [hmapmap] at h1
  have hsc : Units.map σ.toRingHom (Units.mk0 lam hlam) =
      Units.mk0 (σ lam) ((map_ne_zero σ).mpr hlam) := Units.ext rfl
  rw [hsc] at h1
  have h2 : Matrix.GeneralLinearGroup.map σ.toRingHom b * b = S (Units.mk0 lam hlam) := by
    calc Matrix.GeneralLinearGroup.map σ.toRingHom b * b
        = (S (Units.mk0 lam hlam) * b⁻¹) * b := by rw [hb_inv]
      _ = S (Units.mk0 lam hlam) * (b⁻¹ * b) := by rw [mul_assoc]
      _ = S (Units.mk0 lam hlam) := by group
  have hscalar : Matrix.scalar (Fin n) (σ lam) = Matrix.scalar (Fin n) lam := by
    have hEq : Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 (σ lam)
          ((map_ne_zero σ).mpr hlam)) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 lam hlam) := h1.symm.trans h2
    have := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) hEq
    simpa using this
  have h00 := congrFun₂ hscalar ⟨0, by omega⟩ ⟨0, by omega⟩
  simpa [Matrix.scalar_apply] using h00

end Cocycle

section FiniteField

variable {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_unit_norm_eq_of_fixed {σ : F ≃+* F} (hσ : σ.trans σ = RingEquiv.refl F)
    (hσne : σ ≠ 1)
    {lam : F} (hlam : lam ≠ 0) (hfix : σ lam = lam) :
    ∃ t : Fˣ, (t : F) * σ (t : F) = lam := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨f, -, hFc⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hFc]
  obtain ⟨hfeven, hσpow⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution
      (K := F) (f := (f : ℕ)) f.pos hcard hσne
      (mul_self_eq_one_of_trans_self_eq_refl hσ)
  have h2k : 2 * ((f : ℕ) / 2) = (f : ℕ) := Nat.two_mul_div_two_of_even hfeven
  have hkpos : 1 ≤ (f : ℕ) / 2 := by
    by_contra h
    have h0 : (f : ℕ) / 2 = 0 := by omega
    rw [h0, mul_zero] at h2k
    exact f.pos.ne' h2k.symm
  have hud : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 ((f : ℕ) / 2) F :=
    ⟨Nat.prime_two, hkpos, by rw [h2k]; exact hcard⟩
  have hbar : ∀ x : F, hud.bar x = σ x := by
    intro x
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply,
      ← hσpow x]
  have hmem : lam ∈ hud.fixedField := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_fixedField, hbar]
    exact hfix
  obtain ⟨t, ht⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.unitary_field_norm hud).1 ⟨lam, hmem⟩
  have ht' : t * σ t = lam := by
    have := congrArg Subtype.val ht
    simpa only [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.coe_normHom,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm, hbar] using this
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ht'
    exact hlam ht'.symm
  exact ⟨Units.mk0 t ht0, ht'⟩

theorem exists_normalized_of_mul_map_eq_scalar {σ : F ≃+* F}
    (hσ : σ.trans σ = RingEquiv.refl F) (hσne : σ ≠ 1) (hn : 1 ≤ n) {b : GL (Fin n) F} {lam : F}
    (hlam : lam ≠ 0)
    (hb : b * Matrix.GeneralLinearGroup.map σ.toRingHom b =
      Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 lam hlam)) :
    σ lam = lam ∧ ∃ t : Fˣ, (t : F) * σ (t : F) = lam⁻¹ ∧
      (Matrix.GeneralLinearGroup.scalar (Fin n) t * b) *
        Matrix.GeneralLinearGroup.map σ.toRingHom
          (Matrix.GeneralLinearGroup.scalar (Fin n) t * b) = 1 := by
  classical
  have hσlam := map_eq_of_mul_map_eq_scalar (F := F) hσ hn hlam hb
  have hfixinv : σ lam⁻¹ = lam⁻¹ := by rw [map_inv₀, hσlam]
  obtain ⟨t, ht⟩ := exists_unit_norm_eq_of_fixed (F := F) hσ hσne (inv_ne_zero hlam) hfixinv
  refine ⟨hσlam, t, ht, ?_⟩
  have hBB : (Matrix.GeneralLinearGroup.scalar (Fin n) t * b) *
      Matrix.GeneralLinearGroup.map σ.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin n) t * b) = 1 := by
    rw [map_mul, Matrix.GeneralLinearGroup.map_scalar]
    calc Matrix.GeneralLinearGroup.scalar (Fin n) t * b *
          (Matrix.GeneralLinearGroup.scalar (Fin n) (Units.map σ.toRingHom t) *
            Matrix.GeneralLinearGroup.map σ.toRingHom b)
        = Matrix.GeneralLinearGroup.scalar (Fin n) t *
            Matrix.GeneralLinearGroup.scalar (Fin n) (Units.map σ.toRingHom t) *
            (b * Matrix.GeneralLinearGroup.map σ.toRingHom b) := by
          rw [mul_assoc, ← mul_assoc b, ← Matrix.GeneralLinearGroup.scalar_commute]
          group
      _ = 1 := by
          rw [hb, ← map_mul, ← map_mul, ← map_one (Matrix.GeneralLinearGroup.scalar (Fin n))]
          congr 1
          ext
          simp [ht, inv_mul_cancel₀ hlam]
  exact hBB

end FiniteField

section Descent

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_eq_mul_map_inv_of_mul_map_eq_one {σ : F ≃+* F}
    (hσ : σ.trans σ = RingEquiv.refl F) (hσne : σ ≠ 1) {b : GL (Fin n) F}
    (hb : b * Matrix.GeneralLinearGroup.map σ.toRingHom b = 1) :
    ∃ P : GL (Fin n) F, b = P * (Matrix.GeneralLinearGroup.map σ.toRingHom P)⁻¹ := by
  classical
  have hσσx := apply_apply_eq_of_mul_self_eq_one (F := F)
    (mul_self_eq_one_of_trans_self_eq_refl hσ)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F, σ x₀ ≠ x₀ := by
    by_contra hall
    exact hσne (RingEquiv.ext fun x => by
      by_contra hx
      exact hall ⟨x, hx⟩)
  set T : (Fin n → F) → (Fin n → F) := fun v =>
    (b : Matrix (Fin n) (Fin n) F) *ᵥ fun i => σ (v i) with hT
  have hbm : (b : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F).map σ = 1 := by
    have := congrArg Units.val hb
    simpa using this
  have hTT : ∀ v, T (T v) = v := by
    intro v
    have hσBv : (fun i => σ (((b : Matrix (Fin n) (Fin n) F) *ᵥ fun i => σ (v i)) i)) =
        (b : Matrix (Fin n) (Fin n) F).map σ *ᵥ v := by
      funext i
      have h1 := RingHom.map_mulVec (σ : F →+* F) (b : Matrix (Fin n) (Fin n) F)
        (fun i => σ (v i)) i
      simp only [RingEquiv.coe_toRingHom] at h1
      rw [h1]
      congr 2
      funext j
      exact hσσx (v j)
    simp only [hT]
    rw [hσBv, mulVec_mulVec, hbm, one_mulVec]
  have hadd : ∀ v w, T (v + w) = T v + T w := fun v w => by
    simp only [hT, Pi.add_apply, map_add]
    rw [← mulVec_add]
    rfl
  have hsmul : ∀ (a : F) v, T (a • v) = σ a • T v := fun a v => by
    simp only [hT, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← mulVec_smul]
    rfl
  obtain ⟨P, hP⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_fixed_basis_of_ne hx₀ T hadd hsmul hTT
  refine ⟨P, ?_⟩
  have hBP : b * Matrix.GeneralLinearGroup.map σ.toRingHom P = P := by
    ext r c
    have := congrFun (hP c) r
    simp only [hT, mulVec, dotProduct] at this
    rw [← this]
    simp [Matrix.mul_apply]
  rw [eq_mul_inv_iff_mul_eq]
  exact hBP

end Descent

end CFSG.LieType.SpecialLinear
