module

public import CFSG.GH74.GLS.Stage2.OddAut.Lin3
public import CFSG.GH74.GLS.Stage2.OddAut.ElemAbBasis
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Kernel

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem conjAut_eq_one_iff_of_three_le (hn : 3 ≤ n) (A : GL (Fin n) K) :
    conjAut n K A = 1 ↔ ∃ u : Kˣ, A = GeneralLinearGroup.scalar (Fin n) u := by
  constructor
  · intro h
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn A 1 (by rw [map_one, mul_one, h])
    exact ⟨c, hc.symm⟩
  · rintro ⟨u, rfl⟩
    exact conjAut_scalar u

end Kernel

section Lifts

variable {K : Type} [Field K] [Finite K]

theorem exists_lifts {r : ℕ} (hr : r.Prime) (V : Subgroup (MulAut (projectiveSL 3 K)))
    (hVI : V ≤ (conjAut 3 K).range) (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    ∃ (a b : GL (Fin 3) K) (ua ub u : Kˣ), conjAut 3 K a ∈ V ∧ conjAut 3 K b ∈ V ∧
      a ^ r = GeneralLinearGroup.scalar (Fin 3) ua ∧ b ^ r = GeneralLinearGroup.scalar (Fin 3) ub ∧
      a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a) ∧
      (∀ i j : ℕ, (∃ w : Kˣ, a ^ i * b ^ j = GeneralLinearGroup.scalar (Fin 3) w) →
        r ∣ i ∧ r ∣ j) ∧
      ∀ v ∈ V, ∃ i j : ℕ, v = conjAut 3 K (a ^ i * b ^ j) := by
  obtain ⟨v₁, hv₁, v₂, hv₂, hind, hspan⟩ := exists_basis_elemAbelian hr V hVc hVe hVab
  obtain ⟨a, rfl⟩ := hVI hv₁
  obtain ⟨b, rfl⟩ := hVI hv₂
  have hc : conjAut 3 K a * conjAut 3 K b = conjAut 3 K b * conjAut 3 K a := hVab _ hv₁ _ hv₂
  have hone : ∀ A : GL (Fin 3) K, conjAut 3 K A = 1 → ∃ w : Kˣ, A = GeneralLinearGroup.scalar (Fin 3) w :=
    fun A h => (conjAut_eq_one_iff_of_three_le (le_refl 3) A).mp h
  obtain ⟨ua, hua⟩ := hone (a ^ r) (by rw [map_pow]; exact hVe _ hv₁)
  obtain ⟨ub, hub⟩ := hone (b ^ r) (by rw [map_pow]; exact hVe _ hv₂)
  obtain ⟨u, hu⟩ := hone (a * b * a⁻¹ * b⁻¹) (by
    simp only [map_mul, map_inv]
    rw [hc]
    group)
  refine ⟨a, b, ua, ub, u, hv₁, hv₂, hua, hub, ?_, ?_, ?_⟩
  · calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = GeneralLinearGroup.scalar (Fin 3) u * (b * a) := by rw [hu, mul_assoc]
  · rintro i j ⟨w, hw⟩
    apply hind
    have := congrArg (conjAut 3 K) hw
    rw [map_mul, map_pow, map_pow, conjAut_scalar] at this
    exact this
  · intro v hv
    obtain ⟨i, j, hij⟩ := hspan v hv
    exact ⟨i, j, by rw [hij, map_mul, map_pow, map_pow]⟩

end Lifts

section Classify

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem mul_pow_diag {B : Matrix (Fin 3) (Fin 3) K} {M : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K}
    (h : M * B = B * Matrix.diagonal d) (i : ℕ) :
    M ^ i * B = B * Matrix.diagonal (d ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal,
      pow_succ]
    rfl

theorem inner_plane_classify {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : ¬ r ∣ Nat.card K)
    (V : Subgroup (MulAut (projectiveSL 3 K))) (hVI : V ≤ (conjAut 3 K).range)
    (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    (∃ B : GL (Fin 3) K, ∀ v ∈ V, ∃ (x : GL (Fin 3) K) (d : Fin 3 → K), v = conjAut 3 K x ∧
        (x : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
          (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d) ∨
      (r = 3 ∧ ∃ (a b : GL (Fin 3) K) (u : Kˣ), u ≠ 1 ∧ conjAut 3 K a ∈ V ∧ conjAut 3 K b ∈ V ∧
        a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a) ∧
        ∀ v ∈ V, ∃ i j : ℕ, v = conjAut 3 K (a ^ i * b ^ j)) := by
  obtain ⟨a, b, ua, ub, u, ha, hb, hau, hbu, hab, hind, hspan⟩ := exists_lifts hr V hVI hVc hVe hVab
  rcases lin3_classify hr hr2 hrK a b ua ub hau hbu u hab hind with
    ⟨B, da, db, h1, h2⟩ | ⟨hr3, hu⟩
  · left
    refine ⟨B, fun v hv => ?_⟩
    obtain ⟨i, j, hij⟩ := hspan v hv
    refine ⟨a ^ i * b ^ j, da ^ i * db ^ j, hij, ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Matrix.mul_assoc,
      mul_pow_diag h2 j, ← Matrix.mul_assoc, mul_pow_diag h1 i, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    rfl
  · exact Or.inr ⟨hr3, a, b, u, hu, ha, hb, hab, hspan⟩

end Classify

end CFSG.GH74.GLS.Stage2.OddAut
