module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.NineCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers.U43 Matrix

namespace U43Six

@[expose] def m1 : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, ⟨2, 0⟩, ⟨1, 2⟩;
    0, 0, ⟨2, 2⟩, ⟨2, 0⟩;
    0, 0, 0, 0;
    0, 0, 0, 0]

@[expose] def m2 : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, 0, 0;
    0, 0, 0, 0;
    ⟨2, 0⟩, ⟨2, 1⟩, 0, 0;
    ⟨1, 1⟩, ⟨2, 0⟩, 0, 0]

@[expose] def tmat (s : F9) : Matrix (Fin 4) (Fin 4) F9 := 1 + s • m1 - (s ^ 3) • m2

theorem tmat_mul : ∀ s s' : F9, tmat s * tmat s' = tmat (s + s') := by decide +kernel

theorem tmat_zero : tmat 0 = 1 := by decide +kernel

theorem det_tmat : ∀ s : F9, (tmat s).det = 1 := by decide +kernel

theorem tmat_unitary : ∀ s : F9, ((tmat s).map (· ^ 3))ᵀ * tmat s = 1 := by decide +kernel

@[expose] def act (s : F9) (x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) :
    ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 :=
  (x.1 + (s.re ^ 2 + s.im ^ 2) * x.2.1 + s.im * x.2.2.1 - s.re * x.2.2.2, x.2.1,
    x.2.2.1 - s.im * x.2.1, x.2.2.2 + s.re * x.2.1)

theorem tmat_mul_rmat_axes : ∀ (s : F9) (x : ZMod 3),
    (tmat s * rmat x 0 0 0 = rmat (act s (x, 0, 0, 0)).1 (act s (x, 0, 0, 0)).2.1
        (act s (x, 0, 0, 0)).2.2.1 (act s (x, 0, 0, 0)).2.2.2 * tmat s) ∧
    (tmat s * rmat 0 x 0 0 = rmat (act s (0, x, 0, 0)).1 (act s (0, x, 0, 0)).2.1
        (act s (0, x, 0, 0)).2.2.1 (act s (0, x, 0, 0)).2.2.2 * tmat s) ∧
    (tmat s * rmat 0 0 x 0 = rmat (act s (0, 0, x, 0)).1 (act s (0, 0, x, 0)).2.1
        (act s (0, 0, x, 0)).2.2.1 (act s (0, 0, x, 0)).2.2.2 * tmat s) ∧
    (tmat s * rmat 0 0 0 x = rmat (act s (0, 0, 0, x)).1 (act s (0, 0, 0, x)).2.1
        (act s (0, 0, 0, x)).2.2.1 (act s (0, 0, 0, x)).2.2.2 * tmat s) := by decide +kernel

theorem conj_four {M : Type*} [Monoid M] {t r₁ r₂ r₃ r₄ s₁ s₂ s₃ s₄ : M} (h₁ : t * r₁ = s₁ * t)
    (h₂ : t * r₂ = s₂ * t) (h₃ : t * r₃ = s₃ * t) (h₄ : t * r₄ = s₄ * t) :
    t * (r₁ * (r₂ * (r₃ * r₄))) = s₁ * (s₂ * (s₃ * s₄)) * t := by
  calc t * (r₁ * (r₂ * (r₃ * r₄))) = (t * r₁) * (r₂ * (r₃ * r₄)) := by simp only [mul_assoc]
    _ = s₁ * ((t * r₂) * (r₃ * r₄)) := by rw [h₁]; simp only [mul_assoc]
    _ = s₁ * (s₂ * ((t * r₃) * r₄)) := by rw [h₂]; simp only [mul_assoc]
    _ = s₁ * (s₂ * (s₃ * (t * r₄))) := by rw [h₃]; simp only [mul_assoc]
    _ = s₁ * (s₂ * (s₃ * s₄)) * t := by rw [h₄]; simp only [mul_assoc]

theorem tmat_mul_rmat : ∀ (s : F9) (a b c d : ZMod 3),
    tmat s * rmat a b c d = rmat (act s (a, b, c, d)).1 (act s (a, b, c, d)).2.1
      (act s (a, b, c, d)).2.2.1 (act s (a, b, c, d)).2.2.2 * tmat s := by
  intro s a b c d
  have e : rmat a b c d = rmat a 0 0 0 * (rmat 0 b 0 0 * (rmat 0 0 c 0 * rmat 0 0 0 d)) := by
    rw [rmat_mul, rmat_mul, rmat_mul]
    simp only [add_zero, zero_add]
  have e' : rmat (act s (a, b, c, d)).1 (act s (a, b, c, d)).2.1 (act s (a, b, c, d)).2.2.1
      (act s (a, b, c, d)).2.2.2 =
      rmat (act s (a, 0, 0, 0)).1 (act s (a, 0, 0, 0)).2.1 (act s (a, 0, 0, 0)).2.2.1
          (act s (a, 0, 0, 0)).2.2.2 *
        (rmat (act s (0, b, 0, 0)).1 (act s (0, b, 0, 0)).2.1 (act s (0, b, 0, 0)).2.2.1
            (act s (0, b, 0, 0)).2.2.2 *
          (rmat (act s (0, 0, c, 0)).1 (act s (0, 0, c, 0)).2.1 (act s (0, 0, c, 0)).2.2.1
              (act s (0, 0, c, 0)).2.2.2 *
            rmat (act s (0, 0, 0, d)).1 (act s (0, 0, 0, d)).2.1 (act s (0, 0, 0, d)).2.2.1
              (act s (0, 0, 0, d)).2.2.2)) := by
    rw [rmat_mul, rmat_mul, rmat_mul]
    congr 1 <;> simp only [act] <;> ring
  rw [e, e']
  exact conj_four (tmat_mul_rmat_axes s a).1 (tmat_mul_rmat_axes s b).2.1
    (tmat_mul_rmat_axes s c).2.2.1 (tmat_mul_rmat_axes s d).2.2.2

theorem fixed_card_le : ∀ s : F9, s ≠ 0 →
    Fintype.card {x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // act s x = x} ≤ 9 := by decide +kernel

theorem tmat_ne_scalar_rmat : ∀ (s c : F9) (a b d e : ZMod 3),
    tmat s = c • rmat a b d e → s = 0 := by decide +kernel
end U43Six

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
