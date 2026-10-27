module

public import CFSG.GH74.Tits83.DesignC.Delta

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

section Relations

open scoped commutatorElement Pointwise

variable {G G' : Type u} [Group G] [Group G']
variable {U : ℤ → Subgroup G} {U' : ℤ → Subgroup G'}
variable (c : OctCoord U) (c' : OctCoord U') (θ : c.K ≃+* c'.K)

private theorem pair_c12 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (2 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X (1 + s) t, c.X (2 + s) u⁆ = 1
    rw [commutatorElement_def, c.c12 s hs t u]
    group
  · change ⁅c'.X (1 + s) (θ t), c'.X (2 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c12 s hs (θ t) (θ u)]
    group

private theorem pair_c12' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX' c c' θ (2 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X (1 + s) t, c.X' (2 + s) u⁆ = 1
    rw [commutatorElement_def, c.c12' s hs t u]
    group
  · change ⁅c'.X (1 + s) (θ t), c'.X' (2 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c12' s hs (θ t) (θ u)]
    group

private theorem pair_c13 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (3 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X (1 + s) t, c.X (3 + s) u⁆ = 1
    rw [commutatorElement_def, c.c13 s hs t u]
    group
  · change ⁅c'.X (1 + s) (θ t), c'.X (3 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c13 s hs (θ t) (θ u)]
    group

private theorem pair_c14' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX' c c' θ (4 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X (1 + s) t, c.X' (4 + s) u⁆ = 1
    rw [commutatorElement_def, c.c14' s hs t u]
    group
  · change ⁅c'.X (1 + s) (θ t), c'.X' (4 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c14' s hs (θ t) (θ u)]
    group

private theorem pair_c15 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (5 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X (1 + s) t, c.X (5 + s) u⁆ = 1
    rw [commutatorElement_def, c.c15 s hs t u]
    group
  · change ⁅c'.X (1 + s) (θ t), c'.X (5 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c15 s hs (θ t) (θ u)]
    group

private theorem pair_c23 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (3 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X (2 + s) t, c.X (3 + s) u⁆ = 1
    rw [commutatorElement_def, c.c23 s hs t u]
    group
  · change ⁅c'.X (2 + s) (θ t), c'.X (3 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c23 s hs (θ t) (θ u)]
    group

private theorem pair_c2'3 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (3 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X' (2 + s) t, c.X (3 + s) u⁆ = 1
    rw [commutatorElement_def, c.c2'3 s hs t u]
    group
  · change ⁅c'.X' (2 + s) (θ t), c'.X (3 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c2'3 s hs (θ t) (θ u)]
    group

private theorem pair_c2'4 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (4 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X' (2 + s) t, c.X (4 + s) u⁆ = 1
    rw [commutatorElement_def, c.c2'4 s hs t u]
    group
  · change ⁅c'.X' (2 + s) (θ t), c'.X (4 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c2'4 s hs (θ t) (θ u)]
    group

private theorem pair_c2'4' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX' c c' θ (4 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X' (2 + s) t, c.X' (4 + s) u⁆ = 1
    rw [commutatorElement_def, c.c2'4' s hs t u]
    group
  · change ⁅c'.X' (2 + s) (θ t), c'.X' (4 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c2'4' s hs (θ t) (θ u)]
    group

private theorem pair_c24' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX' c c' θ (4 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X (2 + s) t, c.X' (4 + s) u⁆ = 1
    rw [commutatorElement_def, c.c24' s hs t u]
    group
  · change ⁅c'.X (2 + s) (θ t), c'.X' (4 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c24' s hs (θ t) (θ u)]
    group

private theorem pair_c2'5 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (5 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X' (2 + s) t, c.X (5 + s) u⁆ = 1
    rw [commutatorElement_def, c.c2'5 s hs t u]
    group
  · change ⁅c'.X' (2 + s) (θ t), c'.X (5 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c2'5 s hs (θ t) (θ u)]
    group

private theorem pair_c26 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (6 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X (2 + s) t, c.X (6 + s) u⁆ = 1
    rw [commutatorElement_def, c.c26 s hs t u]
    group
  · change ⁅c'.X (2 + s) (θ t), c'.X (6 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c26 s hs (θ t) (θ u)]
    group

private theorem pair_c26' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX' c c' θ (6 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X (2 + s) t, c.X' (6 + s) u⁆ = 1
    rw [commutatorElement_def, c.c26' s hs t u]
    group
  · change ⁅c'.X (2 + s) (θ t), c'.X' (6 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c26' s hs (θ t) (θ u)]
    group

private theorem pair_c2'6 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (6 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X' (2 + s) t, c.X (6 + s) u⁆ = 1
    rw [commutatorElement_def, c.c2'6 s hs t u]
    group
  · change ⁅c'.X' (2 + s) (θ t), c'.X (6 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c2'6 s hs (θ t) (θ u)]
    group

private theorem pair_c2'6' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX' c c' θ (6 + s) u⁆ = 1 := by
  apply Prod.ext
  · change ⁅c.X' (2 + s) t, c.X' (6 + s) u⁆ = 1
    rw [commutatorElement_def, c.c2'6' s hs t u]
    group
  · change ⁅c'.X' (2 + s) (θ t), c'.X' (6 + s) (θ u)⁆ = 1
    rw [commutatorElement_def, c'.c2'6' s hs (θ t) (θ u)]
    group

private theorem pair_r2 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (4 + s) u⁆ =
      gpX' c c' θ (2 + s) (t * u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r2 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r2 s hs (θ t) (θ u)

private theorem pair_r3 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX' c c' θ (6 + s) u⁆ =
      gpX' c c' θ (4 + s) (t * u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r3 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r3 s hs (θ t) (θ u)

private theorem pair_r4 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (6 + s) u⁆ =
      gpX' c c' θ (2 + s) (c.σ t * u) * gpX c c' θ (3 + s) (t * c.σ u) *
      gpX' c c' θ (4 + s) (t * c.σ u * u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r4 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r4 s hs (θ t) (θ u)

private theorem pair_r5 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (7 + s) u⁆ =
      gpX c c' θ (3 + s) (c.σ t * u) * gpX c c' θ (5 + s) (t * c.σ u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r5 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r5 s hs (θ t) (θ u)

private theorem pair_r6 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX' c c' θ (8 + s) u⁆ =
      gpX' c c' θ (2 + s) (c.σ t * t * u) * gpX c c' θ (3 + s) (c.σ t * t * c.σ u) *
      gpX c c' θ (4 + s) (c.σ t * u) * gpX c c' θ (5 + s) (c.σ t * t * u ^ 2) *
      (gpX c c' θ (6 + s) (t * u))⁻¹ * gpX c c' θ (7 + s) (t * c.σ u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r6 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r6 s hs (θ t) (θ u)

private theorem pair_r7 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (8 + s) u⁆ =
      gpX c c' θ (2 + s) (t * u) * gpX c c' θ (3 + s) (c.σ t * t * c.σ u * u ^ 2) *
      (gpX c c' θ (4 + s) (c.σ t * c.σ u * u))⁻¹ *
      gpX c c' θ (5 + s) (c.σ t * t * c.σ u ^ 2 * u ^ 2) *
      gpX' c c' θ (6 + s) (c.σ t * t * c.σ u ^ 2 * u ^ 3) *
      gpX c c' θ (7 + s) (t * c.σ u * u ^ 2) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r7 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r7 s hs (θ t) (θ u)

private theorem pair_r8 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (4 + s) u⁆ =
      gpX c c' θ (3 + s) (t * u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r8 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r8 s hs (θ t) (θ u)

private theorem pair_r9 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (5 + s) u⁆ =
      gpX' c c' θ (4 + s) (t * u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r9 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r9 s hs (θ t) (θ u)

private theorem pair_r10 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (7 + s) u⁆ =
      gpX' c c' θ (4 + s) (t * u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r10 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r10 s hs (θ t) (θ u)

private theorem pair_r11 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (7 + s) u⁆ =
      gpX' c c' θ (4 + s) (c.σ t * t * u) * gpX c c' θ (5 + s) (c.σ t * u) *
      gpX' c c' θ (6 + s) (t * c.σ u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r11 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r11 s hs (θ t) (θ u)

private theorem pair_r12 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX' c c' θ (8 + s) u⁆ =
      gpX' c c' θ (4 + s) (c.σ t * u) * gpX c c' θ (5 + s) (t * u) *
      gpX' c c' θ (6 + s) (t * c.σ u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r12 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r12 s hs (θ t) (θ u)

private theorem pair_r13 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (8 + s) u⁆ =
      gpX c c' θ (3 + s) (t * u) * gpX' c c' θ (4 + s) (c.σ t * c.σ u * u) *
      gpX' c c' θ (6 + s) (t * c.σ u * u ^ 2) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r13 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r13 s hs (θ t) (θ u)

private theorem pair_r14 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX' c c' θ (8 + s) u⁆ =
      gpX' c c' θ (4 + s) (c.σ t * t ^ 2 * u) * gpX' c c' θ (6 + s) (c.σ t * t * c.σ u) *
      gpX c c' θ (7 + s) (t * u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r14 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r14 s hs (θ t) (θ u)

private theorem pair_r15 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (8 + s) u⁆ =
      gpX c c' θ (3 + s) (c.σ t * t * u) * (gpX c c' θ (4 + s) (c.σ t * u))⁻¹ *
      gpX c c' θ (6 + s) (t * c.σ u) * gpX c c' θ (7 + s) (t * c.σ u * u) := by
  apply Prod.ext
  · simpa [gpX, gpX', commutatorElement_def] using c.r15 s hs t u
  · simpa [gpX, gpX', commutatorElement_def, map_mul, map_pow, hθ] using
      c'.r15 s hs (θ t) (θ u)

end Relations

section CommutatorMem

open scoped commutatorElement Pointwise

variable {G G' : Type u} [Group G] [Group G']
variable {U : ℤ → Subgroup G} {U' : ℤ → Subgroup G'}
variable (c : OctCoord U) (c' : OctCoord U') (θ : c.K ≃+* c'.K)

theorem commutator_mem_c12 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (2 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (2 + s) := by
  rw [pair_c12 c c' θ s hs t u]
  exact (DeltaWin c c' θ (1 + s) (2 + s)).one_mem

theorem commutator_mem_c12' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX' c c' θ (2 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (2 + s) := by
  rw [pair_c12' c c' θ s hs t u]
  exact (DeltaWin c c' θ (1 + s) (2 + s)).one_mem

theorem commutator_mem_c13 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (3 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (3 + s) := by
  rw [pair_c13 c c' θ s hs t u]
  exact (DeltaWin c c' θ (1 + s) (3 + s)).one_mem

theorem commutator_mem_c14' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX' c c' θ (4 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (4 + s) := by
  rw [pair_c14' c c' θ s hs t u]
  exact (DeltaWin c c' θ (1 + s) (4 + s)).one_mem

theorem commutator_mem_c15 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (5 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (5 + s) := by
  rw [pair_c15 c c' θ s hs t u]
  exact (DeltaWin c c' θ (1 + s) (5 + s)).one_mem

theorem commutator_mem_c23 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (3 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (3 + s) := by
  rw [pair_c23 c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (3 + s)).one_mem

theorem commutator_mem_c2'3 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (3 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (3 + s) := by
  rw [pair_c2'3 c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (3 + s)).one_mem

theorem commutator_mem_c2'4 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (4 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (4 + s) := by
  rw [pair_c2'4 c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (4 + s)).one_mem

theorem commutator_mem_c2'4' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX' c c' θ (4 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (4 + s) := by
  rw [pair_c2'4' c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (4 + s)).one_mem

theorem commutator_mem_c24' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX' c c' θ (4 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (4 + s) := by
  rw [pair_c24' c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (4 + s)).one_mem

theorem commutator_mem_c2'5 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (5 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (5 + s) := by
  rw [pair_c2'5 c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (5 + s)).one_mem

theorem commutator_mem_c26 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (6 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (6 + s) := by
  rw [pair_c26 c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (6 + s)).one_mem

theorem commutator_mem_c26' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX' c c' θ (6 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (6 + s) := by
  rw [pair_c26' c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (6 + s)).one_mem

theorem commutator_mem_c2'6 (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (6 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (6 + s) := by
  rw [pair_c2'6 c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (6 + s)).one_mem

theorem commutator_mem_c2'6' (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX' c c' θ (6 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (6 + s) := by
  rw [pair_c2'6' c c' θ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (6 + s)).one_mem

theorem commutator_mem_r2 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (4 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (4 + s) := by
  rw [pair_r2 c c' θ hθ s hs t u]
  exact gpX'_mem_DeltaWin c c' θ (i := 1 + s) (j := 4 + s) (k := 2 + s)
      (by omega) (by omega)
      (Even.add (show Even (2 : ℤ) from ⟨1, rfl⟩) hs)
      (t * u)

theorem commutator_mem_r3 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX' c c' θ (6 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (6 + s) := by
  rw [pair_r3 c c' θ hθ s hs t u]
  exact gpX'_mem_DeltaWin c c' θ (i := 1 + s) (j := 6 + s) (k := 4 + s)
      (by omega) (by omega)
      (Even.add (show Even (4 : ℤ) from ⟨2, rfl⟩) hs)
      (t * u)

theorem commutator_mem_r4 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (6 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (6 + s) := by
  rw [pair_r4 c c' θ hθ s hs t u]
  exact (DeltaWin c c' θ (1 + s) (6 + s)).mul_mem
    ((DeltaWin c c' θ (1 + s) (6 + s)).mul_mem
      (gpX'_mem_DeltaWin c c' θ (i := 1 + s) (j := 6 + s) (k := 2 + s)
      (by omega) (by omega)
      (Even.add (show Even (2 : ℤ) from ⟨1, rfl⟩) hs)
      (c.σ t * u))
      (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 6 + s) (k := 3 + s)
      (by omega) (by omega)
      (t * c.σ u)))
    (gpX'_mem_DeltaWin c c' θ (i := 1 + s) (j := 6 + s) (k := 4 + s)
      (by omega) (by omega)
      (Even.add (show Even (4 : ℤ) from ⟨2, rfl⟩) hs)
      (t * c.σ u * u))

theorem commutator_mem_r5 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (7 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (7 + s) := by
  rw [pair_r5 c c' θ hθ s hs t u]
  exact (DeltaWin c c' θ (1 + s) (7 + s)).mul_mem
    (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 7 + s) (k := 3 + s)
      (by omega) (by omega)
      (c.σ t * u))
    (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 7 + s) (k := 5 + s)
      (by omega) (by omega)
      (t * c.σ u))

theorem commutator_mem_r6 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX' c c' θ (8 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (8 + s) := by
  rw [pair_r6 c c' θ hθ s hs t u]
  exact (DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
    ((DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
      ((DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
        ((DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
          ((DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
            (gpX'_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 2 + s)
      (by omega) (by omega)
      (Even.add (show Even (2 : ℤ) from ⟨1, rfl⟩) hs)
      (c.σ t * t * u))
            (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 3 + s)
      (by omega) (by omega)
      (c.σ t * t * c.σ u)))
          (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 4 + s)
      (by omega) (by omega)
      (c.σ t * u)))
        (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 5 + s)
      (by omega) (by omega)
      (c.σ t * t * u ^ 2)))
      ((DeltaWin c c' θ (1 + s) (8 + s)).inv_mem
    (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 6 + s)
      (by omega) (by omega)
      (t * u))))
    (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 7 + s)
      (by omega) (by omega)
      (t * c.σ u))

theorem commutator_mem_r7 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (1 + s) t, gpX c c' θ (8 + s) u⁆ ∈
      DeltaWin c c' θ (1 + s) (8 + s) := by
  rw [pair_r7 c c' θ hθ s hs t u]
  exact (DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
    ((DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
      ((DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
        ((DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
          ((DeltaWin c c' θ (1 + s) (8 + s)).mul_mem
            (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 2 + s)
      (by omega) (by omega)
      (t * u))
            (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 3 + s)
      (by omega) (by omega)
      (c.σ t * t * c.σ u * u ^ 2)))
          ((DeltaWin c c' θ (1 + s) (8 + s)).inv_mem
    (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 4 + s)
      (by omega) (by omega)
      (c.σ t * c.σ u * u))))
        (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 5 + s)
      (by omega) (by omega)
      (c.σ t * t * c.σ u ^ 2 * u ^ 2)))
      (gpX'_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 6 + s)
      (by omega) (by omega)
      (Even.add (show Even (6 : ℤ) from ⟨3, rfl⟩) hs)
      (c.σ t * t * c.σ u ^ 2 * u ^ 3)))
    (gpX_mem_DeltaWin c c' θ (i := 1 + s) (j := 8 + s) (k := 7 + s)
      (by omega) (by omega)
      (t * c.σ u * u ^ 2))

theorem commutator_mem_r8 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (4 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (4 + s) := by
  rw [pair_r8 c c' θ hθ s hs t u]
  exact gpX_mem_DeltaWin c c' θ (i := 2 + s) (j := 4 + s) (k := 3 + s)
      (by omega) (by omega)
      (t * u)

theorem commutator_mem_r9 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (5 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (5 + s) := by
  rw [pair_r9 c c' θ hθ s hs t u]
  exact gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 5 + s) (k := 4 + s)
      (by omega) (by omega)
      (Even.add (show Even (4 : ℤ) from ⟨2, rfl⟩) hs)
      (t * u)

theorem commutator_mem_r10 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (7 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (7 + s) := by
  rw [pair_r10 c c' θ hθ s hs t u]
  exact gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 7 + s) (k := 4 + s)
      (by omega) (by omega)
      (Even.add (show Even (4 : ℤ) from ⟨2, rfl⟩) hs)
      (t * u)

theorem commutator_mem_r11 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (7 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (7 + s) := by
  rw [pair_r11 c c' θ hθ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (7 + s)).mul_mem
    ((DeltaWin c c' θ (2 + s) (7 + s)).mul_mem
      (gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 7 + s) (k := 4 + s)
      (by omega) (by omega)
      (Even.add (show Even (4 : ℤ) from ⟨2, rfl⟩) hs)
      (c.σ t * t * u))
      (gpX_mem_DeltaWin c c' θ (i := 2 + s) (j := 7 + s) (k := 5 + s)
      (by omega) (by omega)
      (c.σ t * u)))
    (gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 7 + s) (k := 6 + s)
      (by omega) (by omega)
      (Even.add (show Even (6 : ℤ) from ⟨3, rfl⟩) hs)
      (t * c.σ u))

theorem commutator_mem_r12 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX' c c' θ (8 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (8 + s) := by
  rw [pair_r12 c c' θ hθ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (8 + s)).mul_mem
    ((DeltaWin c c' θ (2 + s) (8 + s)).mul_mem
      (gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 4 + s)
      (by omega) (by omega)
      (Even.add (show Even (4 : ℤ) from ⟨2, rfl⟩) hs)
      (c.σ t * u))
      (gpX_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 5 + s)
      (by omega) (by omega)
      (t * u)))
    (gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 6 + s)
      (by omega) (by omega)
      (Even.add (show Even (6 : ℤ) from ⟨3, rfl⟩) hs)
      (t * c.σ u))

theorem commutator_mem_r13 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX' c c' θ (2 + s) t, gpX c c' θ (8 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (8 + s) := by
  rw [pair_r13 c c' θ hθ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (8 + s)).mul_mem
    ((DeltaWin c c' θ (2 + s) (8 + s)).mul_mem
      (gpX_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 3 + s)
      (by omega) (by omega)
      (t * u))
      (gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 4 + s)
      (by omega) (by omega)
      (Even.add (show Even (4 : ℤ) from ⟨2, rfl⟩) hs)
      (c.σ t * c.σ u * u)))
    (gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 6 + s)
      (by omega) (by omega)
      (Even.add (show Even (6 : ℤ) from ⟨3, rfl⟩) hs)
      (t * c.σ u * u ^ 2))

theorem commutator_mem_r14 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX' c c' θ (8 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (8 + s) := by
  rw [pair_r14 c c' θ hθ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (8 + s)).mul_mem
    ((DeltaWin c c' θ (2 + s) (8 + s)).mul_mem
      (gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 4 + s)
      (by omega) (by omega)
      (Even.add (show Even (4 : ℤ) from ⟨2, rfl⟩) hs)
      (c.σ t * t ^ 2 * u))
      (gpX'_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 6 + s)
      (by omega) (by omega)
      (Even.add (show Even (6 : ℤ) from ⟨3, rfl⟩) hs)
      (c.σ t * t * c.σ u)))
    (gpX_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 7 + s)
      (by omega) (by omega)
      (t * u))

theorem commutator_mem_r15 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (s : ℤ) (hs : Even s) (t u : c.K) :
    ⁅gpX c c' θ (2 + s) t, gpX c c' θ (8 + s) u⁆ ∈
      DeltaWin c c' θ (2 + s) (8 + s) := by
  rw [pair_r15 c c' θ hθ s hs t u]
  exact (DeltaWin c c' θ (2 + s) (8 + s)).mul_mem
    ((DeltaWin c c' θ (2 + s) (8 + s)).mul_mem
      ((DeltaWin c c' θ (2 + s) (8 + s)).mul_mem
        (gpX_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 3 + s)
      (by omega) (by omega)
      (c.σ t * t * u))
        ((DeltaWin c c' θ (2 + s) (8 + s)).inv_mem
    (gpX_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 4 + s)
      (by omega) (by omega)
      (c.σ t * u))))
      (gpX_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 6 + s)
      (by omega) (by omega)
      (t * c.σ u)))
    (gpX_mem_DeltaWin c c' θ (i := 2 + s) (j := 8 + s) (k := 7 + s)
      (by omega) (by omega)
      (t * c.σ u * u))

end CommutatorMem

end CFSG.GH74.Tits83
