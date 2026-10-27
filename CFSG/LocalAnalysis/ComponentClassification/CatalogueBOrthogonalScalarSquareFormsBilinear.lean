module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsFormula
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

universe u v w

variable {K : Type u} {E : Type v} {V : Type w}
  [Field K] [Field E] [Algebra K E] [AddCommGroup V] [Module K V]

theorem coordinate_expansion (b : Module.Basis (Fin 2) K E) (s : E)
    (h0 : b 0 = 1) (h1 : b 1 = s) (z : E) :
    z = algebraMap K E (b.repr z 0) + algebraMap K E (b.repr z 1) * s := by
  have hz := b.sum_repr z
  simpa only [Fin.sum_univ_two, h0, h1, Algebra.smul_def, mul_one] using hz.symm

theorem coordinate_equality (b : Module.Basis (Fin 2) K E) (s : E)
    (h0 : b 0 = 1) (h1 : b 1 = s) (a c a' c' : K) :
    algebraMap K E a + algebraMap K E c * s =
        algebraMap K E a' + algebraMap K E c' * s ↔ a = a' ∧ c = c' := by
  have hr (a c : K) : b.repr (algebraMap K E a + algebraMap K E c * s) =
      a • Finsupp.single 0 1 + c • Finsupp.single 1 1 := by
    rw [← mul_one (algebraMap K E a), ← h0, ← h1, ← Algebra.smul_def,
      ← Algebra.smul_def, map_add, map_smul, map_smul, b.repr_self, b.repr_self]
  constructor
  · intro h
    have he := congrArg b.repr h
    rw [hr, hr] at he
    constructor
    · simpa using congrArg (fun f : Fin 2 →₀ K => f 0) he
    · simpa using congrArg (fun f : Fin 2 →₀ K => f 1) he
  · rintro ⟨rfl, rfl⟩
    rfl

variable [Module E V] [IsScalarTower K E V]

theorem positiveFormula_esmul_left (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (hd : d ≠ 0) (hs : s ^ 2 = algebraMap K E d)
    (hT : ∀ x, T (T x) = d • x) (hact : ∀ x, s • x = T x)
    (hspan : ∀ z : E, ∃ a c : K, z = algebraMap K E a + algebraMap K E c * s)
    (z : E) (x y : V) :
    positiveFormula B T d s (z • x) y = z * positiveFormula B T d s x y := by
  obtain ⟨a, c, rfl⟩ := hspan z
  rw [add_smul, mul_smul, hact, IsScalarTower.algebraMap_smul E,
    IsScalarTower.algebraMap_smul E, positiveFormula_add_left,
    positiveFormula_smul_left, positiveFormula_smul_left,
    positiveFormula_operator_left B T d s hd hs hT]
  ring

theorem positiveFormula_esmul_right (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (hd : d ≠ 0) (hs : s ^ 2 = algebraMap K E d)
    (hT : ∀ x, T (T x) = d • x) (hact : ∀ x, s • x = T x)
    (hspan : ∀ z : E, ∃ a c : K, z = algebraMap K E a + algebraMap K E c * s)
    (hadj : ∀ x y, B (T x) y = B x (T y)) (z : E) (x y : V) :
    positiveFormula B T d s x (z • y) = z * positiveFormula B T d s x y := by
  obtain ⟨a, c, rfl⟩ := hspan z
  rw [add_smul, mul_smul, hact, IsScalarTower.algebraMap_smul E,
    IsScalarTower.algebraMap_smul E, positiveFormula_add_right,
    positiveFormula_smul_right, positiveFormula_smul_right,
    positiveFormula_operator_right B T d s hd hs hT hadj]
  ring

theorem negativeFormula_esmul_left (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (hd : d ≠ 0) (hs : s ^ 2 = algebraMap K E d)
    (hT : ∀ x, T (T x) = d • x) (hact : ∀ x, s • x = T x)
    (hspan : ∀ z : E, ∃ a c : K, z = algebraMap K E a + algebraMap K E c * s)
    (bar : E ≃ₐ[K] E) (hbar : bar s = -s)
    (hadj : ∀ x y, B (T x) y = -B x (T y)) (z : E) (x y : V) :
    negativeFormula B T d s (z • x) y = bar z * negativeFormula B T d s x y := by
  obtain ⟨a, c, rfl⟩ := hspan z
  rw [add_smul, mul_smul, hact, IsScalarTower.algebraMap_smul E,
    IsScalarTower.algebraMap_smul E, negativeFormula_add_left,
    negativeFormula_smul_left, negativeFormula_smul_left,
    negativeFormula_operator_left B T d s hd hs hT hadj]
  simp only [map_add, map_mul, AlgEquiv.commutes, hbar]
  ring

theorem negativeFormula_esmul_right (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (hd : d ≠ 0) (hs : s ^ 2 = algebraMap K E d)
    (hT : ∀ x, T (T x) = d • x) (hact : ∀ x, s • x = T x)
    (hspan : ∀ z : E, ∃ a c : K, z = algebraMap K E a + algebraMap K E c * s)
    (z : E) (x y : V) :
    negativeFormula B T d s x (z • y) = z * negativeFormula B T d s x y := by
  obtain ⟨a, c, rfl⟩ := hspan z
  rw [add_smul, mul_smul, hact, IsScalarTower.algebraMap_smul E,
    IsScalarTower.algebraMap_smul E, negativeFormula_add_right,
    negativeFormula_smul_right, negativeFormula_smul_right,
    negativeFormula_operator_right B T d s hd hs hT]
  ring

@[expose] def positiveBilinear (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (hd : d ≠ 0) (hs : s ^ 2 = algebraMap K E d)
    (hT : ∀ x, T (T x) = d • x) (hact : ∀ x, s • x = T x)
    (hspan : ∀ z : E, ∃ a c : K, z = algebraMap K E a + algebraMap K E c * s)
    (hadj : ∀ x y, B (T x) y = B x (T y)) : LinearMap.BilinForm E V :=
  LinearMap.mk₂ E (positiveFormula B T d s)
    (positiveFormula_add_left B T d s)
    (fun z x y => by simpa only [smul_eq_mul] using
      positiveFormula_esmul_left B T d s hd hs hT hact hspan z x y)
    (positiveFormula_add_right B T d s)
    (fun z x y => by simpa only [smul_eq_mul] using
      positiveFormula_esmul_right B T d s hd hs hT hact hspan hadj z x y)

@[expose] def negativeSesquilinear (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (hd : d ≠ 0) (hs : s ^ 2 = algebraMap K E d)
    (hT : ∀ x, T (T x) = d • x) (hact : ∀ x, s • x = T x)
    (hspan : ∀ z : E, ∃ a c : K, z = algebraMap K E a + algebraMap K E c * s)
    (bar : E ≃ₐ[K] E) (hbar : bar s = -s)
    (hadj : ∀ x y, B (T x) y = -B x (T y)) :
    V →ₛₗ[(bar : E →+* E)] V →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (bar : E →+* E) (RingHom.id E) (negativeFormula B T d s)
    (negativeFormula_add_left B T d s)
    (fun z x y => by
      rw [smul_eq_mul]
      change negativeFormula B T d s (z • x) y =
        bar z * negativeFormula B T d s x y
      exact negativeFormula_esmul_left B T d s hd hs hT hact hspan bar hbar hadj z x y)
    (negativeFormula_add_right B T d s)
    (fun z x y => by simpa only [smul_eq_mul, RingHom.id_apply] using
      negativeFormula_esmul_right B T d s hd hs hT hact hspan z x y)

section Properties

variable (B : LinearMap.BilinForm K V) (T : Module.End K V) (d : K) (s : E)
  (hd : d ≠ 0) (hs : s ^ 2 = algebraMap K E d) (hT : ∀ x, T (T x) = d • x)
  (hact : ∀ x, s • x = T x)
  (hspan : ∀ z : E, ∃ a c : K, z = algebraMap K E a + algebraMap K E c * s)
  (hadj : ∀ x y, B (T x) y = B x (T y))

theorem positiveBilinear_apply (x y : V) :
    positiveBilinear B T d s hd hs hT hact hspan hadj x y = positiveFormula B T d s x y := rfl

theorem positiveBilinear_isSymm (hB : B.IsSymm) :
    (positiveBilinear B T d s hd hs hT hact hspan hadj).IsSymm :=
  ⟨fun x y => (positiveFormula_symm B T d s hB hadj x y).symm⟩

theorem positiveBilinear_nondegenerate (b : Module.Basis (Fin 2) K E)
    (h0 : b 0 = 1) (h1 : b 1 = s) (hnd : B.Nondegenerate) :
    (positiveBilinear B T d s hd hs hT hact hspan hadj).Nondegenerate := by
  constructor
  · intro x hx
    apply hnd.1 x
    intro y
    have he := hx y
    change algebraMap K E (B x y) + algebraMap K E (d⁻¹ * B (T x) y) * s = 0 at he
    have hc := (coordinate_equality b s h0 h1 (B x y) (d⁻¹ * B (T x) y) 0 0).mp
      (by simpa using he)
    exact hc.1
  · intro y hy
    apply hnd.2 y
    intro x
    have he := hy x
    change algebraMap K E (B x y) + algebraMap K E (d⁻¹ * B (T x) y) * s = 0 at he
    exact ((coordinate_equality b s h0 h1 (B x y) (d⁻¹ * B (T x) y) 0 0).mp
      (by simpa using he)).1

end Properties

section HermitianProperties

variable (B : LinearMap.BilinForm K V) (T : Module.End K V) (d : K) (s : E)
  (hd : d ≠ 0) (hs : s ^ 2 = algebraMap K E d) (hT : ∀ x, T (T x) = d • x)
  (hact : ∀ x, s • x = T x)
  (hspan : ∀ z : E, ∃ a c : K, z = algebraMap K E a + algebraMap K E c * s)
  (bar : E ≃ₐ[K] E) (hbar : bar s = -s)
  (hadj : ∀ x y, B (T x) y = -B x (T y))

theorem negativeSesquilinear_apply (x y : V) :
    negativeSesquilinear B T d s hd hs hT hact hspan bar hbar hadj x y =
      negativeFormula B T d s x y := rfl

theorem negativeSesquilinear_isSymm (hB : B.IsSymm) :
    (negativeSesquilinear B T d s hd hs hT hact hspan bar hbar hadj).IsSymm :=
  ⟨fun x y => (negativeFormula_hermitian B T d s bar hbar hB hadj x y).symm⟩

theorem negativeSesquilinear_nondegenerate (b : Module.Basis (Fin 2) K E)
    (h0 : b 0 = 1) (h1 : b 1 = s) (hnd : B.Nondegenerate) :
    (negativeSesquilinear B T d s hd hs hT hact hspan bar hbar hadj).Nondegenerate := by
  constructor
  · intro x hx
    apply hnd.1 x
    intro y
    have he := hx y
    change algebraMap K E (B x y) + algebraMap K E (d⁻¹ * B x (T y)) * s = 0 at he
    exact ((coordinate_equality b s h0 h1 (B x y) (d⁻¹ * B x (T y)) 0 0).mp
      (by simpa using he)).1
  · intro y hy
    apply hnd.2 y
    intro x
    have he := hy x
    change algebraMap K E (B x y) + algebraMap K E (d⁻¹ * B x (T y)) * s = 0 at he
    exact ((coordinate_equality b s h0 h1 (B x y) (d⁻¹ * B x (T y)) 0 0).mp
      (by simpa using he)).1

end HermitianProperties

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
