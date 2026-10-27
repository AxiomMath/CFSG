module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareField

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V} {A : Module.End K V} {d : K}

theorem smul_one_add_smul_congr {a b a' b' : K} (ha : a = a') (hb : b = b') :
    a • (1 : Module.End K V) + b • A = a' • 1 + b' • A := by
  rw [ha, hb]

theorem smul_eq_of_coords {x : scalarSquareField A} {a b : K}
    (hx : (x : Module.End K V) = a • 1 + b • A) (v : V) : x • v = a • v + b • A v := by
  change (x : Module.End K V) v = _
  rw [hx, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply]

theorem apply_apply_of_sq (hAA : A * A = d • 1) (v : V) : A (A v) = d • v := by
  rw [← Module.End.mul_apply, hAA, LinearMap.smul_apply, Module.End.one_apply]

theorem coords_eq_zero [Nontrivial V] (hA : ∀ c : K, A ≠ c • 1) {a b : K}
    (h : a • (1 : Module.End K V) + b • A = 0) : a = 0 ∧ b = 0 :=
  smul_add_smul_inj hA (by rw [h, zero_smul, zero_smul, add_zero])

section Alt

variable (B A d) in
@[expose] noncomputable def altFieldForm (v w : V) : scalarSquareField A :=
  ⟨B v w • 1 + (d⁻¹ * B (A v) w) • A, smul_add_smul_mem _ _⟩

theorem coe_altFieldForm (v w : V) :
    (altFieldForm B A d v w : Module.End K V) = B v w • 1 + (d⁻¹ * B (A v) w) • A :=
  rfl

theorem exists_altFieldBilin (hAA : A * A = d • 1) (hd0 : d ≠ 0)
    (hadj : ∀ v w, B (A v) w = B v (A w)) :
    ∃ BE : LinearMap.BilinForm (scalarSquareField A) V, ∀ v w, BE v w = altFieldForm B A d v w := by
  refine ⟨LinearMap.mk₂ (scalarSquareField A) (altFieldForm B A d) ?_ ?_ ?_ ?_, fun _ _ => rfl⟩
  · intro m₁ m₂ n
    apply Subtype.ext
    change B (m₁ + m₂) n • (1 : Module.End K V) + (d⁻¹ * B (A (m₁ + m₂)) n) • A =
      (B m₁ n • 1 + (d⁻¹ * B (A m₁) n) • A) + (B m₂ n • 1 + (d⁻¹ * B (A m₂) n) • A)
    simp only [map_add, LinearMap.add_apply, mul_add, add_smul]
    abel
  · intro c m n
    obtain ⟨a, b, hab⟩ := (mem_scalarSquareField_iff hAA).mp c.2
    apply Subtype.ext
    rw [smul_eq_mul, smul_eq_of_coords hab]
    change B (a • m + b • A m) n • (1 : Module.End K V) +
        (d⁻¹ * B (A (a • m + b • A m)) n) • A =
      (c : Module.End K V) * (B m n • 1 + (d⁻¹ * B (A m) n) • A)
    rw [hab, smul_add_smul_mul hAA]
    simp only [map_add, map_smul, apply_apply_of_sq hAA, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    refine smul_one_add_smul_congr ?_ ?_
    · field_simp
    · field_simp
  · intro m n₁ n₂
    apply Subtype.ext
    change B m (n₁ + n₂) • (1 : Module.End K V) + (d⁻¹ * B (A m) (n₁ + n₂)) • A =
      (B m n₁ • 1 + (d⁻¹ * B (A m) n₁) • A) + (B m n₂ • 1 + (d⁻¹ * B (A m) n₂) • A)
    simp only [map_add, mul_add, add_smul]
    abel
  · intro c m n
    obtain ⟨a, b, hab⟩ := (mem_scalarSquareField_iff hAA).mp c.2
    apply Subtype.ext
    rw [smul_eq_mul, smul_eq_of_coords hab]
    change B m (a • n + b • A n) • (1 : Module.End K V) +
        (d⁻¹ * B (A m) (a • n + b • A n)) • A =
      (c : Module.End K V) * (B m n • 1 + (d⁻¹ * B (A m) n) • A)
    rw [hab, smul_add_smul_mul hAA]
    simp only [map_add, map_smul, smul_eq_mul, ← hadj, apply_apply_of_sq hAA,
      LinearMap.smul_apply]
    refine smul_one_add_smul_congr ?_ ?_
    · field_simp
    · field_simp

theorem altFieldForm_self (h2 : (2 : K) ≠ 0) (hB : B.IsAlt) (hadj : ∀ v w, B (A v) w = B v (A w))
    (v : V) : altFieldForm B A d v v = 0 := by
  have h1 : B (A v) v = 0 := by
    have e1 := hadj v v
    have e2 := LinearMap.IsAlt.neg hB (A v) v
    have e3 : (2 : K) * B (A v) v = 0 := by linear_combination e1 - e2
    exact (mul_eq_zero.mp e3).resolve_left h2
  apply Subtype.ext
  rw [coe_altFieldForm, hB v, h1, mul_zero, zero_smul, zero_smul, add_zero]
  rfl

theorem altFieldForm_eq_zero [Nontrivial V] (hA : ∀ c : K, A ≠ c • 1) {v w : V}
    (h : altFieldForm B A d v w = 0) : B v w = 0 :=
  (coords_eq_zero hA (congrArg Subtype.val h)).1

theorem altFieldForm_eq_iff [Nontrivial V] (hA : ∀ c : K, A ≠ c • 1) {v w v' w' : V} :
    altFieldForm B A d v w = altFieldForm B A d v' w' ↔
      B v w = B v' w' ∧ d⁻¹ * B (A v) w = d⁻¹ * B (A v') w' :=
  ⟨fun h => smul_add_smul_inj hA (congrArg Subtype.val h), fun ⟨h1, h2⟩ =>
    Subtype.ext (by rw [coe_altFieldForm, coe_altFieldForm, h1, h2])⟩

end Alt

section Herm

variable (B A) in
@[expose] noncomputable def hermFieldForm (v w : V) : scalarSquareField A :=
  ⟨B v (A w) • 1 + B v w • A, smul_add_smul_mem _ _⟩

theorem coe_hermFieldForm (v w : V) :
    (hermFieldForm B A v w : Module.End K V) = B v (A w) • 1 + B v w • A :=
  rfl

theorem exists_hermFieldSesq (hAA : A * A = d • 1)
    (bar : scalarSquareField A →+* scalarSquareField A)
    (hbar : ∀ (x : scalarSquareField A) (a b : K), (x : Module.End K V) = a • 1 + b • A →
      (bar x : Module.End K V) = a • 1 - b • A)
    (hadj : ∀ v w, B (A v) w = -B v (A w)) (hAμ : ∀ v w, B (A v) (A w) = -d * B v w) :
    ∃ hf : V →ₛₗ[bar] V →ₗ[scalarSquareField A] scalarSquareField A,
      ∀ v w, hf v w = hermFieldForm B A v w := by
  refine ⟨LinearMap.mk₂'ₛₗ bar (RingHom.id _) (hermFieldForm B A) ?_ ?_ ?_ ?_, fun _ _ => rfl⟩
  · intro m₁ m₂ n
    apply Subtype.ext
    change B (m₁ + m₂) (A n) • (1 : Module.End K V) + B (m₁ + m₂) n • A =
      (B m₁ (A n) • 1 + B m₁ n • A) + (B m₂ (A n) • 1 + B m₂ n • A)
    simp only [map_add, LinearMap.add_apply, add_smul]
    abel
  · intro c m n
    obtain ⟨a, b, hab⟩ := (mem_scalarSquareField_iff hAA).mp c.2
    apply Subtype.ext
    rw [smul_eq_mul, smul_eq_of_coords hab]
    change B (a • m + b • A m) (A n) • (1 : Module.End K V) + B (a • m + b • A m) n • A =
      (bar c : Module.End K V) * (B m (A n) • 1 + B m n • A)
    rw [hbar c a b hab, sub_eq_add_neg, ← neg_smul, smul_add_smul_mul hAA]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hAμ,
      hadj]
    refine smul_one_add_smul_congr ?_ ?_ <;> ring
  · intro m n₁ n₂
    apply Subtype.ext
    change B m (A (n₁ + n₂)) • (1 : Module.End K V) + B m (n₁ + n₂) • A =
      (B m (A n₁) • 1 + B m n₁ • A) + (B m (A n₂) • 1 + B m n₂ • A)
    simp only [map_add, add_smul]
    abel
  · intro c m n
    obtain ⟨a, b, hab⟩ := (mem_scalarSquareField_iff hAA).mp c.2
    apply Subtype.ext
    rw [RingHom.id_apply, smul_eq_mul, smul_eq_of_coords hab]
    change B m (A (a • n + b • A n)) • (1 : Module.End K V) + B m (a • n + b • A n) • A =
      (c : Module.End K V) * (B m (A n) • 1 + B m n • A)
    rw [hab, smul_add_smul_mul hAA]
    simp only [map_add, map_smul, apply_apply_of_sq hAA, smul_eq_mul]
    refine smul_one_add_smul_congr ?_ ?_ <;> ring

theorem hermFieldForm_symm (hB : B.IsAlt) (bar : scalarSquareField A →+* scalarSquareField A)
    (hbar : ∀ (x : scalarSquareField A) (a b : K), (x : Module.End K V) = a • 1 + b • A →
      (bar x : Module.End K V) = a • 1 - b • A)
    (hadj : ∀ v w, B (A v) w = -B v (A w)) (v w : V) :
    bar (hermFieldForm B A v w) = hermFieldForm B A w v := by
  apply Subtype.ext
  rw [hbar _ _ _ (coe_hermFieldForm v w), coe_hermFieldForm, sub_eq_add_neg, ← neg_smul]
  refine smul_one_add_smul_congr ?_ ?_
  · rw [← LinearMap.IsAlt.neg hB, hadj, neg_neg]
  · rw [LinearMap.IsAlt.neg hB]

theorem hermFieldForm_eq_zero [Nontrivial V] (hA : ∀ c : K, A ≠ c • 1) {v w : V}
    (h : hermFieldForm B A v w = 0) : B v w = 0 :=
  (coords_eq_zero hA (congrArg Subtype.val h)).2

theorem hermFieldForm_eq_iff [Nontrivial V] (hA : ∀ c : K, A ≠ c • 1) {v w v' w' : V} :
    hermFieldForm B A v w = hermFieldForm B A v' w' ↔
      B v (A w) = B v' (A w') ∧ B v w = B v' w' :=
  ⟨fun h => smul_add_smul_inj hA (congrArg Subtype.val h), fun ⟨h1, h2⟩ =>
    Subtype.ext (by rw [coe_hermFieldForm, coe_hermFieldForm, h1, h2])⟩

end Herm

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
