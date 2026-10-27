module

public import CFSG.GH74.Tits83.DesignC.Relations
public import TauCeti.GroupTheory.Commutator
public import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair
open scoped commutatorElement Pointwise
universe u
section Generator

variable {G G' : Type u} [Group G] [Group G']
variable {U : ℤ → Subgroup G} {U' : ℤ → Subgroup G'}
variable (c : OctCoord U) (c' : OctCoord U') (θ : c.K ≃+* c'.K)
private theorem gen_commutator_mem_1 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (j : ℤ) (hij : (1 : ℤ) < j) (hj : j ≤ 8)
    {x y : G × G'} (hx : x ∈ Gen c c' θ 1) (hy : y ∈ Gen c c' θ j) :
    ⁅x, y⁆ ∈ DeltaWin c c' θ 1 j := by
    interval_cases j
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · simpa using commutator_mem_c12 c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_c12' c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c13 c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r2 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_c14' c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c15 c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r4 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_r3 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r5 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r7 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_r6 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega

private theorem gen_commutator_mem_2 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (j : ℤ) (hij : (2 : ℤ) < j) (hj : j ≤ 8)
    {x y : G × G'} (hx : x ∈ Gen c c' θ 2) (hy : y ∈ Gen c c' θ j) :
    ⁅x, y⁆ ∈ DeltaWin c c' θ 2 j := by
    interval_cases j
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c23 c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'3 c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r8 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_c24' c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'4 c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_c2'4' c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r9 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'5 c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c26 c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_c26' c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'6 c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_c2'6' c c' θ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r11 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r10 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r15 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_r14 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r13 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u
        · exact commutator_mem_r12 c c' θ hθ 0 (show Even (0 : ℤ) from ⟨0, rfl⟩) t u

private theorem gen_commutator_mem_3 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (j : ℤ) (hij : (3 : ℤ) < j) (hj : j ≤ 8)
    {x y : G × G'} (hx : x ∈ Gen c c' θ 3) (hy : y ∈ Gen c c' θ j) :
    ⁅x, y⁆ ∈ DeltaWin c c' θ 3 j := by
    interval_cases j
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c12 c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exact commutator_mem_c12' c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c13 c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r2 c c' θ hθ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exact commutator_mem_c14' c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c15 c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r4 c c' θ hθ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exact commutator_mem_r3 c c' θ hθ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega

private theorem gen_commutator_mem_4 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (j : ℤ) (hij : (4 : ℤ) < j) (hj : j ≤ 8)
    {x y : G × G'} (hx : x ∈ Gen c c' θ 4) (hy : y ∈ Gen c c' θ j) :
    ⁅x, y⁆ ∈ DeltaWin c c' θ 4 j := by
    interval_cases j
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c23 c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'3 c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r8 c c' θ hθ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exact commutator_mem_c24' c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'4 c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exact commutator_mem_c2'4' c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r9 c c' θ hθ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'5 c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c26 c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exact commutator_mem_c26' c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'6 c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u
        · exact commutator_mem_c2'6' c c' θ 2 (show Even (2 : ℤ) from ⟨1, rfl⟩) t u

private theorem gen_commutator_mem_5 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (j : ℤ) (hij : (5 : ℤ) < j) (hj : j ≤ 8)
    {x y : G × G'} (hx : x ∈ Gen c c' θ 5) (hy : y ∈ Gen c c' θ j) :
    ⁅x, y⁆ ∈ DeltaWin c c' θ 5 j := by
    interval_cases j
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c12 c c' θ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
        · exact commutator_mem_c12' c c' θ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c13 c c' θ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · exfalso; obtain ⟨a, ha⟩ := hie; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r2 c c' θ hθ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
        · exact commutator_mem_c14' c c' θ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega

private theorem gen_commutator_mem_6 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (j : ℤ) (hij : (6 : ℤ) < j) (hj : j ≤ 8)
    {x y : G × G'} (hx : x ∈ Gen c c' θ 6) (hy : y ∈ Gen c c' θ j) :
    ⁅x, y⁆ ∈ DeltaWin c c' θ 6 j := by
    interval_cases j
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c23 c c' θ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'3 c c' θ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
        · exfalso; obtain ⟨a, ha⟩ := hje; omega
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_r8 c c' θ hθ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
        · exact commutator_mem_c24' c c' θ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c2'4 c c' θ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u
        · exact commutator_mem_c2'4' c c' θ 4 (show Even (4 : ℤ) from ⟨2, rfl⟩) t u

private theorem gen_commutator_mem_7 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (j : ℤ) (hij : (7 : ℤ) < j) (hj : j ≤ 8)
    {x y : G × G'} (hx : x ∈ Gen c c' θ 7) (hy : y ∈ Gen c c' θ j) :
    ⁅x, y⁆ ∈ DeltaWin c c' θ 7 j := by
    interval_cases j
    ·
      simp only [Gen, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨t, rfl⟩ | ⟨hie, t, rfl⟩
      · rcases hy with ⟨u, rfl⟩ | ⟨hje, u, rfl⟩
        · exact commutator_mem_c12 c c' θ 6 (show Even (6 : ℤ) from ⟨3, rfl⟩) t u
        · exact commutator_mem_c12' c c' θ 6 (show Even (6 : ℤ) from ⟨3, rfl⟩) t u
      · exfalso; obtain ⟨a, ha⟩ := hie; omega

theorem gen_commutator_mem (c : OctCoord U) (c' : OctCoord U') (θ : c.K ≃+* c'.K)
    (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) (i j : ℤ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 8)
    {x y : G × G'} (hx : x ∈ Gen c c' θ i) (hy : y ∈ Gen c c' θ j) :
    ⁅x, y⁆ ∈ DeltaWin c c' θ i j := by
  have hi8 : i ≤ 8 := by omega
  interval_cases i
  · exact gen_commutator_mem_1 c c' θ hθ j hij hj hx hy
  · exact gen_commutator_mem_2 c c' θ hθ j hij hj hx hy
  · exact gen_commutator_mem_3 c c' θ hθ j hij hj hx hy
  · exact gen_commutator_mem_4 c c' θ hθ j hij hj hx hy
  · exact gen_commutator_mem_5 c c' θ hθ j hij hj hx hy
  · exact gen_commutator_mem_6 c c' θ hθ j hij hj hx hy
  · exact gen_commutator_mem_7 c c' θ hθ j hij hj hx hy
  · exfalso; omega


end Generator
section InductionA

open CFSG.GH74.BNPair
open scoped commutatorElement Pointwise
variable {G G' : Type u} [Group G] [Group G']
variable {U : ℤ → Subgroup G} {U' : ℤ → Subgroup G'}
variable (c : OctCoord U) (c' : OctCoord U') (θ : c.K ≃+* c'.K)

theorem DeltaWin_mono {i j j' : ℤ} (h : j ≤ j') :
    DeltaWin c c' θ i j ≤ DeltaWin c c' θ i j' := by
  rw [DeltaWin]
  refine iSup₂_le fun k hk => ?_
  have hk' := mem_intList_iff.1 hk
  exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList (i + 1) (j' - 1)) =>
    Delta c c' θ k) k (mem_intList_iff.2 ⟨hk'.1, by omega⟩) le_rfl

theorem DeltaWin_mono_left {i i' j : ℤ} (h : i ≤ i') :
    DeltaWin c c' θ i' j ≤ DeltaWin c c' θ i j := by
  rw [DeltaWin]
  refine iSup₂_le fun k hk => ?_
  have hk' := mem_intList_iff.1 hk
  exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList (i + 1) (j - 1)) =>
    Delta c c' θ k) k (mem_intList_iff.2 ⟨by omega, hk'.2⟩) le_rfl

theorem Delta_le_normalizer_DeltaWin {i j : ℤ}
    (h : ∀ k ∈ intList (i + 1) (j - 1),
      ⁅Delta c c' θ i, Delta c c' θ k⁆ ≤ DeltaWin c c' θ i j) :
    Delta c c' θ i ≤
      Subgroup.normalizer (DeltaWin c c' θ i j : Set (G × G')) := by
  refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun a ha => ?_
  rw [DeltaWin, Subgroup.map_iSup]
  refine iSup_le fun k => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hk => ?_
  refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun x hx => ?_
  have hcomm : ⁅a, x⁆ ∈ DeltaWin c c' θ i j :=
    (Subgroup.commutator_le.1 (h k hk)) a ha x hx
  have hxW : x ∈ DeltaWin c c' θ i j := by
    rw [DeltaWin]
    exact (le_iSup₂_of_le (f := fun k (_ : k ∈ intList (i + 1) (j - 1)) =>
      Delta c c' θ k) k hk le_rfl) hx
  have e : a * x * a⁻¹ = ⁅a, x⁆ * x := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (DeltaWin c c' θ i j).mul_mem hcomm hxW

theorem Delta_le_normalizer_DeltaWin_right {i j : ℤ}
    (h : ∀ k ∈ intList (i + 1) (j - 1),
      ⁅Delta c c' θ k, Delta c c' θ j⁆ ≤ DeltaWin c c' θ i j) :
    Delta c c' θ j ≤
      Subgroup.normalizer (DeltaWin c c' θ i j : Set (G × G')) := by
  refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun a ha => ?_
  rw [DeltaWin, Subgroup.map_iSup]
  refine iSup_le fun k => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hk => ?_
  refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun x hx => ?_
  have hcomm : ⁅x, a⁆ ∈ DeltaWin c c' θ i j :=
    (Subgroup.commutator_le.1 (h k hk)) x hx a ha
  have hxW : x ∈ DeltaWin c c' θ i j := by
    rw [DeltaWin]
    exact (le_iSup₂_of_le (f := fun k (_ : k ∈ intList (i + 1) (j - 1)) =>
      Delta c c' θ k) k hk le_rfl) hx
  have e : a * x * a⁻¹ = ⁅x, a⁆⁻¹ * x := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (DeltaWin c c' θ i j).mul_mem ((DeltaWin c c' θ i j).inv_mem hcomm) hxW

theorem DeltaWin_adjacent_bot (i : ℤ) : DeltaWin c c' θ i (i + 1) = ⊥ := by
  apply le_antisymm
  · rw [DeltaWin]
    refine iSup₂_le fun k hk => ?_
    have hk' := mem_intList_iff.1 hk
    exfalso
    omega
  · exact bot_le

theorem Delta_commutator_1_2 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 1, Delta c c' θ 2⁆ ≤ DeltaWin c c' θ 1 2 := by
  have hbot : DeltaWin c c' θ 1 2 = ⊥ := by
    simpa using DeltaWin_adjacent_bot c c' θ 1
  have hA : Delta c c' θ 1 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (2) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  have hB : Delta c c' θ 2 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (2) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 1 2
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_2_3 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 2, Delta c c' θ 3⁆ ≤ DeltaWin c c' θ 2 3 := by
  have hbot : DeltaWin c c' θ 2 3 = ⊥ := by
    simpa using DeltaWin_adjacent_bot c c' θ 2
  have hA : Delta c c' θ 2 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (3) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  have hB : Delta c c' θ 3 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (3) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 2 3
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_3_4 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 3, Delta c c' θ 4⁆ ≤ DeltaWin c c' θ 3 4 := by
  have hbot : DeltaWin c c' θ 3 4 = ⊥ := by
    simpa using DeltaWin_adjacent_bot c c' θ 3
  have hA : Delta c c' θ 3 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (4) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  have hB : Delta c c' θ 4 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (4) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 3 4
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_4_5 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 4, Delta c c' θ 5⁆ ≤ DeltaWin c c' θ 4 5 := by
  have hbot : DeltaWin c c' θ 4 5 = ⊥ := by
    simpa using DeltaWin_adjacent_bot c c' θ 4
  have hA : Delta c c' θ 4 ≤
      Subgroup.normalizer (DeltaWin c c' θ 4 (5) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  have hB : Delta c c' θ 5 ≤
      Subgroup.normalizer (DeltaWin c c' θ 4 (5) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 4 5
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_5_6 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 5, Delta c c' θ 6⁆ ≤ DeltaWin c c' θ 5 6 := by
  have hbot : DeltaWin c c' θ 5 6 = ⊥ := by
    simpa using DeltaWin_adjacent_bot c c' θ 5
  have hA : Delta c c' θ 5 ≤
      Subgroup.normalizer (DeltaWin c c' θ 5 (6) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  have hB : Delta c c' θ 6 ≤
      Subgroup.normalizer (DeltaWin c c' θ 5 (6) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 5 6
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_6_7 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 6, Delta c c' θ 7⁆ ≤ DeltaWin c c' θ 6 7 := by
  have hbot : DeltaWin c c' θ 6 7 = ⊥ := by
    simpa using DeltaWin_adjacent_bot c c' θ 6
  have hA : Delta c c' θ 6 ≤
      Subgroup.normalizer (DeltaWin c c' θ 6 (7) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  have hB : Delta c c' θ 7 ≤
      Subgroup.normalizer (DeltaWin c c' θ 6 (7) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 6 7
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_7_8 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 7, Delta c c' θ 8⁆ ≤ DeltaWin c c' θ 7 8 := by
  have hbot : DeltaWin c c' θ 7 8 = ⊥ := by
    simpa using DeltaWin_adjacent_bot c c' θ 7
  have hA : Delta c c' θ 7 ≤
      Subgroup.normalizer (DeltaWin c c' θ 7 (8) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  have hB : Delta c c' θ 8 ≤
      Subgroup.normalizer (DeltaWin c c' θ 7 (8) : Set (G × G')) := by
    rw [hbot]
    exact Subgroup.le_normalizer_of_normal
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 7 8
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_1_3 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 1, Delta c c' θ 3⁆ ≤ DeltaWin c c' θ 1 3 := by
  have hA : Delta c c' θ 1 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (3) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 1) (j := 3) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_1_2 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 2) (j' := 3) c c' θ (by norm_num))
  have hB : Delta c c' θ 3 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (3) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 1) (j := 3) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_3 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 2) (j := 3) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 1 3
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_2_4 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 2, Delta c c' θ 4⁆ ≤ DeltaWin c c' θ 2 4 := by
  have hA : Delta c c' θ 2 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (4) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 2) (j := 4) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 3) (j' := 4) c c' θ (by norm_num))
  have hB : Delta c c' θ 4 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (4) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 2) (j := 4) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_3_4 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 3) (j := 4) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 2 4
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_3_5 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 3, Delta c c' θ 5⁆ ≤ DeltaWin c c' θ 3 5 := by
  have hA : Delta c c' θ 3 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (5) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 3) (j := 5) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_3_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 4) (j' := 5) c c' θ (by norm_num))
  have hB : Delta c c' θ 5 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (5) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 3) (j := 5) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_4_5 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 4) (j := 5) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 3 5
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_4_6 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 4, Delta c c' θ 6⁆ ≤ DeltaWin c c' θ 4 6 := by
  have hA : Delta c c' θ 4 ≤
      Subgroup.normalizer (DeltaWin c c' θ 4 (6) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 4) (j := 6) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_4_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 4) (j := 5) (j' := 6) c c' θ (by norm_num))
  have hB : Delta c c' θ 6 ≤
      Subgroup.normalizer (DeltaWin c c' θ 4 (6) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 4) (j := 6) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_5_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 4) (i' := 5) (j := 6) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 4 6
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_5_7 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 5, Delta c c' θ 7⁆ ≤ DeltaWin c c' θ 5 7 := by
  have hA : Delta c c' θ 5 ≤
      Subgroup.normalizer (DeltaWin c c' θ 5 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 5) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_5_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 5) (j := 6) (j' := 7) c c' θ (by norm_num))
  have hB : Delta c c' θ 7 ≤
      Subgroup.normalizer (DeltaWin c c' θ 5 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 5) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_6_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 5) (i' := 6) (j := 7) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 5 7
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_6_8 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 6, Delta c c' θ 8⁆ ≤ DeltaWin c c' θ 6 8 := by
  have hA : Delta c c' θ 6 ≤
      Subgroup.normalizer (DeltaWin c c' θ 6 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 6) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_6_7 c c' θ hθ).trans
        (DeltaWin_mono (i := 6) (j := 7) (j' := 8) c c' θ (by norm_num))
  have hB : Delta c c' θ 8 ≤
      Subgroup.normalizer (DeltaWin c c' θ 6 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 6) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_7_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 6) (i' := 7) (j := 8) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 6 8
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_1_4 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 1, Delta c c' θ 4⁆ ≤ DeltaWin c c' θ 1 4 := by
  have hA : Delta c c' θ 1 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (4) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 1) (j := 4) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_1_2 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 2) (j' := 4) c c' θ (by norm_num))
    · exact (Delta_commutator_1_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 3) (j' := 4) c c' θ (by norm_num))
  have hB : Delta c c' θ 4 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (4) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 1) (j := 4) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_4 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 2) (j := 4) c c' θ (by norm_num))
    · exact (Delta_commutator_3_4 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 3) (j := 4) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 1 4
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_2_5 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 2, Delta c c' θ 5⁆ ≤ DeltaWin c c' θ 2 5 := by
  have hA : Delta c c' θ 2 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (5) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 2) (j := 5) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 3) (j' := 5) c c' θ (by norm_num))
    · exact (Delta_commutator_2_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 4) (j' := 5) c c' θ (by norm_num))
  have hB : Delta c c' θ 5 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (5) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 2) (j := 5) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_3_5 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 3) (j := 5) c c' θ (by norm_num))
    · exact (Delta_commutator_4_5 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 4) (j := 5) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 2 5
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_3_6 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 3, Delta c c' θ 6⁆ ≤ DeltaWin c c' θ 3 6 := by
  have hA : Delta c c' θ 3 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (6) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 3) (j := 6) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_3_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 4) (j' := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_3_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 5) (j' := 6) c c' θ (by norm_num))
  have hB : Delta c c' θ 6 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (6) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 3) (j := 6) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_4_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 4) (j := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_5_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 5) (j := 6) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 3 6
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_4_7 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 4, Delta c c' θ 7⁆ ≤ DeltaWin c c' θ 4 7 := by
  have hA : Delta c c' θ 4 ≤
      Subgroup.normalizer (DeltaWin c c' θ 4 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 4) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_4_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 4) (j := 5) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_4_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 4) (j := 6) (j' := 7) c c' θ (by norm_num))
  have hB : Delta c c' θ 7 ≤
      Subgroup.normalizer (DeltaWin c c' θ 4 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 4) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_5_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 4) (i' := 5) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_6_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 4) (i' := 6) (j := 7) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 4 7
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_5_8 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 5, Delta c c' θ 8⁆ ≤ DeltaWin c c' θ 5 8 := by
  have hA : Delta c c' θ 5 ≤
      Subgroup.normalizer (DeltaWin c c' θ 5 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 5) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_5_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 5) (j := 6) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_5_7 c c' θ hθ).trans
        (DeltaWin_mono (i := 5) (j := 7) (j' := 8) c c' θ (by norm_num))
  have hB : Delta c c' θ 8 ≤
      Subgroup.normalizer (DeltaWin c c' θ 5 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 5) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_6_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 5) (i' := 6) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_7_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 5) (i' := 7) (j := 8) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 5 8
      (by norm_num) (by norm_num) (by norm_num) hx hy)

end InductionA

end CFSG.GH74.Tits83
