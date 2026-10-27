module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.FieldTheory.Finite.GaloisField

public section

open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

namespace KL3G2

@[expose] def z0 (R : Type) [CommRing R] : SL(3, R) :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

@[expose] def d0 (R : Type) [CommRing R] : SL(3, R) :=
  ⟨!![-1, 0, 0; 0, 0, 1; 0, 1, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_z0 (R : Type) [CommRing R] :
    ((z0 R : SL(3, R)) : Matrix (Fin 3) (Fin 3) R) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := rfl

theorem coe_d0 (R : Type) [CommRing R] :
    ((d0 R : SL(3, R)) : Matrix (Fin 3) (Fin 3) R) = !![-1, 0, 0; 0, 0, 1; 0, 1, 1] := rfl

theorem map_z0 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (z0 R) = z0 S := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_z0, coe_z0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem map_d0 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (d0 R) = d0 S := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_d0, coe_d0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem z0_sq_zmod : z0 (ZMod 3) ^ 2 = 1 := by decide
theorem z0_ne_one_zmod : z0 (ZMod 3) ≠ 1 := by decide
theorem d0_comm_zmod : z0 (ZMod 3) * d0 (ZMod 3) = d0 (ZMod 3) * z0 (ZMod 3) := by decide
theorem d0_pow8_zmod : d0 (ZMod 3) ^ 8 = 1 := by decide
theorem d0_pow4_zmod : d0 (ZMod 3) ^ 4 ≠ 1 := by decide

end KL3G2

namespace KL3G2

open Matrix

@[expose] def IsScl {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : Prop :=
  ∃ c : R, (g : Matrix (Fin n) (Fin n) R) = c • (1 : Matrix (Fin n) (Fin n) R)

theorem mk_eq_one_iff {R : Type} [Field R] (g : GL (Fin 2) R) :
    Matrix.ProjGenLinGroup.mk g = 1 ↔ IsScl g := by
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h1 : (g : Matrix (Fin 2) (Fin 2) R) * ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hc, zero_smul, zero_mul] at h1
      have := congrFun (congrFun h1 0) 0
      simp at this
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, hc]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

theorem isScl_map {R K : Type} [Field R] [Field K] (φ : R ≃+* K) (g : GL (Fin 2) R) :
    IsScl (Matrix.GeneralLinearGroup.map (φ : R →+* K) g) ↔ IsScl g := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨φ.symm c, ?_⟩
    ext i j
    have := congrFun (congrFun hc i) j
    simp [Matrix.GeneralLinearGroup.map] at this
    by_cases hij : i = j
    · subst hij
      simpa using (φ.injective (by simpa using this))
    · simp [hij] at this ⊢
      exact φ.injective (by simpa using this)
  · rintro ⟨c, hc⟩
    refine ⟨φ c, ?_⟩
    ext i j
    have := congrFun (congrFun hc i) j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.GeneralLinearGroup.map, this]
    · simp [Matrix.GeneralLinearGroup.map, hij] at this ⊢
      simpa using congrArg φ this

end KL3G2

namespace KL3G2

open Matrix

instance {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {n : ℕ} (g : GL (Fin n) R) :
    Decidable (IsScl g) := by
  unfold IsScl
  infer_instance

theorem pgl2_zmod3 : ∀ A B : GL (Fin 2) (ZMod 3), IsScl (B * B) → ¬ IsScl B →
    IsScl (A * B * (B * A)⁻¹) → IsScl (A ^ 4) := by
  decide +kernel

theorem exists_zmod_iso {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Nonempty (F ≃+* ZMod 3) := by
  have : Fintype F := Fintype.ofFinite F
  have h : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF]
  exact ⟨FiniteField.ringEquivOfCardEq h⟩

theorem pgl2_cent_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    (g c : PGL(2, F)) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (h : g * c = c * g) : g ^ 4 = 1 := by
  obtain ⟨φ⟩ := exists_zmod_iso hF
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk A =>
  induction c using Matrix.ProjGenLinGroup.induction_on with | mk B =>
  have hBB : IsScl (B * B) := by
    rw [← mk_eq_one_iff, map_mul, ← pow_two]
    exact hc2
  have hB1 : ¬ IsScl B := fun hs => hc1 ((mk_eq_one_iff B).2 hs)
  have hAB : IsScl (A * B * (B * A)⁻¹) := by
    rw [← mk_eq_one_iff, map_mul, map_inv, map_mul, map_mul, h, mul_inv_cancel]
  rw [← isScl_map φ] at hBB hAB
  have hB1' : ¬ IsScl (Matrix.GeneralLinearGroup.map (φ : F →+* ZMod 3) B) := by
    rw [isScl_map φ]; exact hB1
  have := pgl2_zmod3 (Matrix.GeneralLinearGroup.map (φ : F →+* ZMod 3) A)
    (Matrix.GeneralLinearGroup.map (φ : F →+* ZMod 3) B) (by simpa using hBB) hB1'
    (by simpa using hAB)
  rw [← map_pow, isScl_map φ] at this
  rw [← map_pow, mk_eq_one_iff]
  exact this

end KL3G2

namespace KL3G2

open Matrix

theorem sl2_pow8 : ∀ s : SL(2, ZMod 3), s ^ 8 = 1 → s ^ 4 = 1 := by decide +kernel

theorem map_injective_sl {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin n) f) := by
  intro a b h
  apply Subtype.ext
  have := congrArg Subtype.val h
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe] at this
  exact Matrix.map_injective hf this

theorem sl2_orderOf_ne_eight {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) (s : SL(2, F)) :
    orderOf s ≠ 8 := by
  obtain ⟨φ⟩ := exists_zmod_iso hF
  let ψ : SL(2, F) →* SL(2, ZMod 3) := Matrix.SpecialLinearGroup.map (φ : F →+* ZMod 3)
  have hψ : Function.Injective ψ := map_injective_sl _ φ.injective 2
  intro h8
  have h1 : s ^ 8 = 1 := by rw [← h8]; exact pow_orderOf_eq_one s
  have h2 : ψ s ^ 4 = 1 := sl2_pow8 (ψ s) (by rw [← map_pow, h1, map_one])
  have h3 : s ^ 4 = 1 := hψ (by rw [map_pow, h2, map_one])
  have := orderOf_dvd_of_pow_eq_one h3
  rw [h8] at this
  omega

theorem orderOf_z0 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) : orderOf (z0 F) = 2 := by
  obtain ⟨φ⟩ := exists_zmod_iso hF
  let ψ : SL(3, ZMod 3) →* SL(3, F) := Matrix.SpecialLinearGroup.map (φ.symm : ZMod 3 →+* F)
  have hψ : Function.Injective ψ := map_injective_sl _ φ.symm.injective 3
  have hz : z0 F = ψ (z0 (ZMod 3)) := (map_z0 _).symm
  rw [hz, orderOf_injective ψ hψ]
  exact orderOf_eq_prime (by simpa [pow_two] using z0_sq_zmod) z0_ne_one_zmod

theorem orderOf_d0 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) : orderOf (d0 F) = 8 := by
  obtain ⟨φ⟩ := exists_zmod_iso hF
  let ψ : SL(3, ZMod 3) →* SL(3, F) := Matrix.SpecialLinearGroup.map (φ.symm : ZMod 3 →+* F)
  have hψ : Function.Injective ψ := map_injective_sl _ φ.symm.injective 3
  have hd : d0 F = ψ (d0 (ZMod 3)) := (map_d0 _).symm
  rw [hd, orderOf_injective ψ hψ]
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := d0 (ZMod 3)) (by simpa using d0_pow4_zmod)
    (by simpa using d0_pow8_zmod)
  simpa using this

theorem z0_d0_comm {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    z0 F * d0 F = d0 F * z0 F := by
  obtain ⟨φ⟩ := exists_zmod_iso hF
  let ψ : SL(3, ZMod 3) →* SL(3, F) := Matrix.SpecialLinearGroup.map (φ.symm : ZMod 3 →+* F)
  rw [← map_z0 φ.symm.toRingHom, ← map_d0 φ.symm.toRingHom, ← map_mul, ← map_mul, d0_comm_zmod]

end KL3G2

end CFSG.GH74.Generic.S1
