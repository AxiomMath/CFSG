module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Frame

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.OddAut

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_exists_lifts {r : ℕ} (hr : r.Prime)
    (V : Subgroup (MulAut (U3T h))) (hVI : V ≤ primeFormD h ((1 : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K))
    (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    ∃ (a b : U3U h) (ua ub u : Kˣ),
      primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a ∈ V ∧
      primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) b ∈ V ∧
      (a : GL (Fin 3) K) ^ r = GeneralLinearGroup.scalar (Fin 3) ua ∧
      (b : GL (Fin 3) K) ^ r = GeneralLinearGroup.scalar (Fin 3) ub ∧
      (a : GL (Fin 3) K) * b = GeneralLinearGroup.scalar (Fin 3) u * ((b : GL (Fin 3) K) * a) ∧
      (∀ i j : ℕ, (∃ w : Kˣ, (a : GL (Fin 3) K) ^ i * (b : GL (Fin 3) K) ^ j =
        GeneralLinearGroup.scalar (Fin 3) w) → r ∣ i ∧ r ∣ j) ∧
      ∀ v ∈ V, ∃ i j : ℕ, v = primeFormConjHom h ((1 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) (a ^ i * b ^ j) := by
  obtain ⟨v₁, hv₁, v₂, hv₂, hind, hspan⟩ := exists_basis_elemAbelian hr V hVc hVe hVab
  obtain ⟨a, rfl⟩ := hVI hv₁
  obtain ⟨b, rfl⟩ := hVI hv₂
  set c := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hc
  have hone : ∀ A : U3U h, c A = 1 → ∃ w : Kˣ, (A : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) w := fun A hA => (u3_conj_eq_one_iff h A).1 hA
  have hcomm : c a * c b = c b * c a := hVab _ hv₁ _ hv₂
  obtain ⟨ua, hua⟩ := hone (a ^ r) (by rw [map_pow]; exact hVe _ hv₁)
  obtain ⟨ub, hub⟩ := hone (b ^ r) (by rw [map_pow]; exact hVe _ hv₂)
  obtain ⟨u, hu⟩ := hone (a * b * a⁻¹ * b⁻¹) (by
    simp only [map_mul, map_inv]
    rw [hcomm]
    group)
  refine ⟨a, b, ua, ub, u, hv₁, hv₂, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hua
  · simpa using hub
  · have hu' : (a : GL (Fin 3) K) * b * (a : GL (Fin 3) K)⁻¹ * (b : GL (Fin 3) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) u := by simpa using hu
    calc (a : GL (Fin 3) K) * b = ((a : GL (Fin 3) K) * b * (a : GL (Fin 3) K)⁻¹ *
          (b : GL (Fin 3) K)⁻¹) * b * a := by group
      _ = GeneralLinearGroup.scalar (Fin 3) u * ((b : GL (Fin 3) K) * a) := by
          rw [hu', mul_assoc]
  · rintro i j ⟨w, hw⟩
    apply hind
    have := (u3_conj_eq_one_iff h (a ^ i * b ^ j)).2 ⟨w, by simpa using hw⟩
    rw [map_mul, map_pow, map_pow] at this
    exact this
  · intro v hv
    obtain ⟨i, j, hij⟩ := hspan v hv
    exact ⟨i, j, by rw [hij, map_mul, map_pow, map_pow]⟩

theorem u3_plane_classify [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : ¬ r ∣ Nat.card K)
    (V : Subgroup (MulAut (U3T h))) (hVI : V ≤ primeFormD h ((1 : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K))
    (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    (∃ E : U3U h, ∀ v ∈ V, ∃ (x : U3U h) (d : Fin 3 → K),
        v = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∧
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((E : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
          ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d) ∨
      (r = 3 ∧ ∃ (a b : U3U h) (u : Kˣ), u ≠ 1 ∧
        primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a ∈ V ∧
        primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) b ∈ V ∧
        (a : GL (Fin 3) K) * b = GeneralLinearGroup.scalar (Fin 3) u * ((b : GL (Fin 3) K) * a) ∧
        ∀ v ∈ V, ∃ i j : ℕ, v = primeFormConjHom h ((1 : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) (a ^ i * b ^ j)) := by
  obtain ⟨a, b, ua, ub, u, ha, hb, hau, hbu, hab, hind, hspan⟩ :=
    u3_exists_lifts h hr V hVI hVc hVe hVab
  rcases lin3_classify hr hr2 hrK (a : GL (Fin 3) K) (b : GL (Fin 3) K) ua ub hau hbu u hab hind
    with ⟨B, da, db, h1, h2⟩ | ⟨hr3, hu⟩
  · left
    obtain ⟨E, ea, eb, hE, e1, e2⟩ := u3_orthonormal_frame h hr (a : GL (Fin 3) K)
      (b : GL (Fin 3) K) a.2 b.2 ua ub hau hbu hind B da db h1 h2
    refine ⟨⟨E, hE⟩, fun v hv => ?_⟩
    obtain ⟨i, j, hij⟩ := hspan v hv
    refine ⟨a ^ i * b ^ j, fun k => ea k ^ i * eb k ^ j, hij, ?_⟩
    show ((a : GL (Fin 3) K) ^ i * (b : GL (Fin 3) K) ^ j : GL (Fin 3) K).val * E.val = _
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Matrix.mul_assoc,
      mul_pow_diag e2 j, ← Matrix.mul_assoc, mul_pow_diag e1 i, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    rfl
  · exact Or.inr ⟨hr3, a, b, u, hu, ha, hb, hab, hspan⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
