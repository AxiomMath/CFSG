module

public import CFSG.GH74.GLS.SP.Local.SPLCoordDef
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup
open scoped commutatorElement

structure SPLGData {G : Type} [Group G] {F : Type} [Field F] (X₁ X₂ X₃ X₄ R₂ P : Subgroup G)
    (x₁ x₃ x₄ : F → G) (dg : Fˣ → G) (q : ℕ) : Prop where
  card_F : Nat.card F = q
  two_ne : (2 : F) ≠ 0
  add₁ : ∀ s s', x₁ (s + s') = x₁ s * x₁ s'
  add₃ : ∀ a a', x₃ (a + a') = x₃ a * x₃ a'
  add₄ : ∀ b b', x₄ (b + b') = x₄ b * x₄ b'
  rng₁ : ∀ g, g ∈ X₁ ↔ ∃ s, x₁ s = g
  rng₃ : ∀ g, g ∈ X₃ ↔ ∃ a, x₃ a = g
  rng₄ : ∀ g, g ∈ X₄ ↔ ∃ b, x₄ b = g
  X₁_le : X₁ ≤ P
  X₂_le : X₂ ≤ R₂
  X₃_le : X₃ ≤ R₂
  X₄_le : X₄ ≤ R₂
  R₂_le : R₂ ≤ P
  card₂ : Nat.card X₂ = q
  cardR : Nat.card R₂ = q ^ 3
  cardP : Nat.card P = q ^ 4
  cen₂ : ∀ y ∈ X₂, ∀ r ∈ P, y * r = r * y
  comm_R : ∀ r ∈ R₂, ∀ r' ∈ R₂, ⁅r, r'⁆ ∈ X₂
  X₂_comm : X₂ ≤ ⁅R₂, R₂⁆
  fac₂ : ∀ r ∈ R₂, ∃ y ∈ X₂, ∃ a b, r = y * x₃ a * x₄ b
  fac_P : ∀ g ∈ P, ∃ s, ∃ r ∈ R₂, g = x₁ s * r
  c13 : ∀ s a, x₁ s * x₃ a = x₃ a * x₁ s
  dg_X₁ : ∀ u s, dg u * x₁ s * (dg u)⁻¹ = x₁ ((u : F) ^ 2 * s)
  dg_X₃ : ∀ u a, dg u * x₃ a * (dg u)⁻¹ = x₃ ((u : F) * a)
  dg_X₄ : ∀ u b, dg u * x₄ b * (dg u)⁻¹ = x₄ ((u : F)⁻¹ * b)
  dg_X₂ : ∀ u, ∀ y ∈ X₂, dg u * y = y * dg u
  u_X₄ : ∀ s b, ∃ y ∈ X₂, x₁ s * x₄ b * (x₁ s)⁻¹ = x₃ (s * b) * x₄ b * y

abbrev cx₂ {G : Type} [Group G] {F : Type} [Field F] (x₃ x₄ : F → G) (c : F) : G := ⁅x₃ c, x₄ 1⁆

theorem quad_term_eq {F : Type*} [Field F] (two_ne : (2 : F) ≠ 0) (f : F → F → F)
    (hb : ∀ s b b', f s (b + b') = f s b + f s b' - s * b * b')
    (hs : ∀ s s' b, f (s + s') b = f s b + f s' b)
    (ht : ∀ u : Fˣ, ∀ s b, f ((u : F) ^ 2 * s) ((u : F)⁻¹ * b) = f s b) :
    ∀ s b, f s b = -(s * b ^ 2 / 2) := by
  set g : F → F → F := fun s b => f s b + s * b ^ 2 / 2 with hg
  have ga : ∀ s b b', g s (b + b') = g s b + g s b' := by
    intro s b b'
    simp only [hg]
    rw [hb]
    field_simp
    ring
  have gs : ∀ s s' b, g (s + s') b = g s b + g s' b := by
    intro s s' b
    simp only [hg]
    rw [hs]
    ring
  have gt : ∀ u : Fˣ, ∀ s b, g ((u : F) ^ 2 * s) ((u : F)⁻¹ * b) = g s b := by
    intro u s b
    simp only [hg]
    rw [ht]
    have hu : (u : F) ≠ 0 := u.ne_zero
    field_simp
  have f0 : ∀ s, f s 0 = 0 := by
    intro s
    have := hb s 0 0
    simp at this
    linear_combination this
  have f00 : ∀ b, f 0 b = 0 := by
    intro b
    have := hs 0 0 b
    simp at this
    linear_combination this
  have g0 : ∀ s, g s 0 = 0 := by intro s; simp [hg, f0]
  have g00 : ∀ b, g 0 b = 0 := by intro b; simp [hg, f00]
  have key : ∀ s b, g s b = g (b ^ 2 * s) 1 := by
    intro s b
    by_cases hb0 : b = 0
    · subst hb0
      simp [g0, g00]
    · have := gt (Units.mk0 b hb0) s b
      simp only [Units.val_mk0] at this
      rw [inv_mul_cancel₀ hb0] at this
      rw [← this]
  have hψ : ∀ s, g s 1 = 0 := by
    intro s
    have h1 := ga s 1 1
    have h2 := key s (1 + 1)
    have h3 := key s 1
    have h4 : g (4 * s) 1 = 4 * g s 1 := by
      have := gs s s 1
      have h5 := gs (s + s) (s + s) 1
      calc g (4 * s) 1 = g (s + s + (s + s)) 1 := by ring_nf
        _ = g (s + s) 1 + g (s + s) 1 := h5
        _ = 4 * g s 1 := by rw [this]; ring
    have h6 : g s (1 + 1) = 4 * g s 1 := by
      rw [h2]
      have : (1 + 1 : F) ^ 2 * s = 4 * s := by ring
      rw [this, h4]
    have h7 : g s (1 + 1) = 2 * g s 1 := by rw [h1]; ring
    have h8 : 2 * g s 1 = 0 := by linear_combination h7 - h6
    exact (mul_eq_zero.mp h8).resolve_left two_ne
  intro s b
  have h1 : g s b = 0 := by rw [key s b, hψ]
  simp only [hg] at h1
  linear_combination h1

namespace SPLGData

variable {G : Type} [Group G] {F : Type} [Field F] {X₁ X₂ X₃ X₄ R₂ P : Subgroup G}
  {x₁ x₃ x₄ : F → G} {dg : Fˣ → G} {q : ℕ}
  (h : SPLGData X₁ X₂ X₃ X₄ R₂ P x₁ x₃ x₄ dg q)

include h

theorem x₃_zero : x₃ 0 = 1 := by
  have := h.add₃ 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := x₃ 0) (by rw [mul_one]; exact this.symm)

theorem x₄_zero : x₄ 0 = 1 := by
  have := h.add₄ 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := x₄ 0) (by rw [mul_one]; exact this.symm)

theorem x₃_mem_R (a : F) : x₃ a ∈ R₂ := h.X₃_le ((h.rng₃ _).2 ⟨a, rfl⟩)
theorem x₄_mem_R (b : F) : x₄ b ∈ R₂ := h.X₄_le ((h.rng₄ _).2 ⟨b, rfl⟩)
theorem x₁_mem_P (s : F) : x₁ s ∈ P := h.X₁_le ((h.rng₁ _).2 ⟨s, rfl⟩)
theorem x₃_mem_P (a : F) : x₃ a ∈ P := h.R₂_le (h.x₃_mem_R a)
theorem x₄_mem_P (b : F) : x₄ b ∈ P := h.R₂_le (h.x₄_mem_R b)

theorem comm₃₃ (a a' : F) : x₃ a * x₃ a' = x₃ a' * x₃ a := by
  rw [← h.add₃, ← h.add₃, add_comm]

theorem comm₄₄ (b b' : F) : x₄ b * x₄ b' = x₄ b' * x₄ b := by
  rw [← h.add₄, ← h.add₄, add_comm]

theorem ω_mem (a b : F) : ⁅x₃ a, x₄ b⁆ ∈ X₂ := h.comm_R _ (h.x₃_mem_R a) _ (h.x₄_mem_R b)

theorem ω_cen (a b : F) (g : G) (hg : g ∈ P) : ⁅x₃ a, x₄ b⁆ * g = g * ⁅x₃ a, x₄ b⁆ :=
  h.cen₂ _ (h.ω_mem a b) g hg

theorem X₂_mem_P {y : G} (hy : y ∈ X₂) : y ∈ P := h.R₂_le (h.X₂_le hy)

theorem ω_comm (a b a' b' : F) :
    ⁅x₃ a, x₄ b⁆ * ⁅x₃ a', x₄ b'⁆ = ⁅x₃ a', x₄ b'⁆ * ⁅x₃ a, x₄ b⁆ :=
  h.ω_cen a b _ (h.X₂_mem_P (h.ω_mem a' b'))

theorem ω_add_left (a a' b : F) : ⁅x₃ (a + a'), x₄ b⁆ = ⁅x₃ a, x₄ b⁆ * ⁅x₃ a', x₄ b⁆ := by
  rw [h.add₃]
  have e : ⁅x₃ a * x₃ a', x₄ b⁆ = x₃ a * ⁅x₃ a', x₄ b⁆ * (x₃ a)⁻¹ * ⁅x₃ a, x₄ b⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hc := h.ω_cen a' b (x₃ a) (h.x₃_mem_P a)
  have : x₃ a * ⁅x₃ a', x₄ b⁆ * (x₃ a)⁻¹ = ⁅x₃ a', x₄ b⁆ := by
    rw [← hc]; group
  rw [this, h.ω_comm]

theorem ω_zero_left (b : F) : ⁅x₃ 0, x₄ b⁆ = 1 := by
  rw [h.x₃_zero]; simp [commutatorElement_def]

theorem ω_zero_right (a : F) : ⁅x₃ a, x₄ 0⁆ = 1 := by
  rw [h.x₄_zero]; simp [commutatorElement_def]

theorem ω_torus (u : Fˣ) (a b : F) : ⁅x₃ ((u : F) * a), x₄ ((u : F)⁻¹ * b)⁆ = ⁅x₃ a, x₄ b⁆ := by
  have h1 : dg u * ⁅x₃ a, x₄ b⁆ * (dg u)⁻¹ = ⁅x₃ ((u : F) * a), x₄ ((u : F)⁻¹ * b)⁆ := by
    rw [← h.dg_X₃, ← h.dg_X₄]
    simp only [commutatorElement_def]; group
  rw [← h1, h.dg_X₂ u _ (h.ω_mem a b)]
  group

theorem ω_eq_θ (a b : F) : ⁅x₃ a, x₄ b⁆ = ⁅x₃ (a * b), x₄ 1⁆ := by
  by_cases hb : b = 0
  · subst hb
    rw [mul_zero, h.ω_zero_right, h.ω_zero_left]
  · have h1 := h.ω_torus (Units.mk0 b hb) a b
    simp only [Units.val_mk0, inv_mul_cancel₀ hb] at h1
    rw [← h1, mul_comm b a]

theorem θ_mem (c : F) : ⁅x₃ c, x₄ 1⁆ ∈ X₂ := h.ω_mem c 1

theorem θ_add (c c' : F) : ⁅x₃ (c + c'), x₄ 1⁆ = ⁅x₃ c, x₄ 1⁆ * ⁅x₃ c', x₄ 1⁆ := h.ω_add_left c c' 1

theorem θ_zero : ⁅x₃ 0, x₄ 1⁆ = 1 := h.ω_zero_left 1

noncomputable def θhom : Multiplicative F →* G where
  toFun c := ⁅x₃ c.toAdd, x₄ 1⁆
  map_one' := h.θ_zero
  map_mul' c c' := h.θ_add c.toAdd c'.toAdd

theorem comm_mul_left' {r r' r'' : G} (hr : r ∈ R₂) (hr'' : r'' ∈ R₂) (hr' : r' ∈ R₂) :
    ⁅r * r', r''⁆ = ⁅r, r''⁆ * ⁅r', r''⁆ := by
  have e : ⁅r * r', r''⁆ = r * ⁅r', r''⁆ * r⁻¹ * ⁅r, r''⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hc := h.cen₂ _ (h.comm_R r' hr' r'' hr'') r (h.R₂_le hr)
  have : r * ⁅r', r''⁆ * r⁻¹ = ⁅r', r''⁆ := by
    rw [← hc]; group
  rw [this]
  exact h.cen₂ _ (h.comm_R r' hr' r'' hr'') _ (h.X₂_mem_P (h.comm_R r hr r'' hr''))

theorem comm_mul_right' {r r' r'' : G} (hr : r ∈ R₂) (hr' : r' ∈ R₂) (hr'' : r'' ∈ R₂) :
    ⁅r, r' * r''⁆ = ⁅r, r'⁆ * ⁅r, r''⁆ := by
  have e : ⁅r, r' * r''⁆ = ⁅r, r'⁆ * (r' * ⁅r, r''⁆ * r'⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hc := h.cen₂ _ (h.comm_R r hr r'' hr'') r' (h.R₂_le hr')
  have : r' * ⁅r, r''⁆ * r'⁻¹ = ⁅r, r''⁆ := by
    rw [← hc]; group
  rw [this]

theorem comm_central_left {y r : G} (hy : y ∈ X₂) (hr : r ∈ R₂) : ⁅y, r⁆ = 1 := by
  have := h.cen₂ y hy r (h.R₂_le hr)
  simp only [commutatorElement_def]
  rw [this]; group

theorem comm_central_right {y r : G} (hy : y ∈ X₂) (hr : r ∈ R₂) : ⁅r, y⁆ = 1 := by
  have := h.cen₂ y hy r (h.R₂_le hr)
  simp only [commutatorElement_def]
  rw [← this]; group

theorem ω_mem_range (a b : F) : ⁅x₃ a, x₄ b⁆ ∈ h.θhom.range :=
  ⟨Multiplicative.ofAdd (a * b), by simp [θhom, h.ω_eq_θ a b]⟩

theorem comm_R_le_range : ⁅R₂, R₂⁆ ≤ h.θhom.range := by
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  obtain ⟨y, hy, a, b, rfl⟩ := h.fac₂ g hg
  obtain ⟨y', hy', a', b', rfl⟩ := h.fac₂ g' hg'
  have hy₁ : y ∈ R₂ := h.X₂_le hy
  have hy₁' : y' ∈ R₂ := h.X₂_le hy'
  have hA : y * x₃ a ∈ R₂ := R₂.mul_mem hy₁ (h.x₃_mem_R a)
  have hB : y' * x₃ a' ∈ R₂ := R₂.mul_mem hy₁' (h.x₃_mem_R a')
  have hg₂ : y' * x₃ a' * x₄ b' ∈ R₂ := R₂.mul_mem hB (h.x₄_mem_R b')
  have e1 : ⁅y * x₃ a * x₄ b, y' * x₃ a' * x₄ b'⁆ =
      ⁅y * x₃ a, y' * x₃ a' * x₄ b'⁆ * ⁅x₄ b, y' * x₃ a' * x₄ b'⁆ :=
    h.comm_mul_left' hA hg₂ (h.x₄_mem_R b)
  have e2 : ⁅y * x₃ a, y' * x₃ a' * x₄ b'⁆ = ⁅x₃ a, y' * x₃ a' * x₄ b'⁆ := by
    rw [h.comm_mul_left' hy₁ hg₂ (h.x₃_mem_R a), h.comm_central_left hy hg₂, one_mul]
  have e3 : ⁅x₃ a, y' * x₃ a' * x₄ b'⁆ = ⁅x₃ a, x₄ b'⁆ := by
    rw [h.comm_mul_right' (h.x₃_mem_R a) hB (h.x₄_mem_R b'),
      h.comm_mul_right' (h.x₃_mem_R a) hy₁' (h.x₃_mem_R a'), h.comm_central_right hy' (h.x₃_mem_R a),
      commutatorElement_eq_one_iff_mul_comm.mpr (h.comm₃₃ a a'), one_mul, one_mul]
  have e4 : ⁅x₄ b, y' * x₃ a' * x₄ b'⁆ = ⁅x₃ a', x₄ b⁆⁻¹ := by
    rw [h.comm_mul_right' (h.x₄_mem_R b) hB (h.x₄_mem_R b'),
      h.comm_mul_right' (h.x₄_mem_R b) hy₁' (h.x₃_mem_R a'), h.comm_central_right hy' (h.x₄_mem_R b),
      commutatorElement_eq_one_iff_mul_comm.mpr (h.comm₄₄ b b'), one_mul, mul_one, commutatorElement_inv]
  rw [e1, e2, e3, e4]
  exact (h.θhom.range).mul_mem (h.ω_mem_range a b') ((h.θhom.range).inv_mem (h.ω_mem_range a' b))

theorem X₂_le_range : X₂ ≤ h.θhom.range := h.X₂_comm.trans h.comm_R_le_range

theorem θ_surj : ∀ y ∈ X₂, ∃ c : F, ⁅x₃ c, x₄ 1⁆ = y := by
  intro y hy
  obtain ⟨c, rfl⟩ := h.X₂_le_range hy
  exact ⟨c.toAdd, rfl⟩

theorem θ_inj [Finite F] : Function.Injective (fun c : F => ⁅x₃ c, x₄ 1⁆) := by
  classical
  let f : F → ↥X₂ := fun c => ⟨⁅x₃ c, x₄ 1⁆, h.θ_mem c⟩
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨c, hc⟩ := h.θ_surj y.1 y.2
    exact ⟨c, Subtype.ext hc⟩
  have hc : Nat.card F = Nat.card X₂ := by rw [h.card_F, h.card₂]
  have : Finite ↥X₂ := Nat.finite_of_card_ne_zero (by rw [← hc]; exact Nat.card_pos.ne')
  have hf : Function.Injective f := hs.injective_of_finite (Finite.card_eq.mp hc).some
  intro c c' hcc
  exact hf (Subtype.ext hcc)

theorem x₂_add (c c' : F) : cx₂ x₃ x₄ (c + c') = cx₂ x₃ x₄ c * cx₂ x₃ x₄ c' := h.θ_add c c'

theorem x₂_zero : cx₂ x₃ x₄ 0 = 1 := h.θ_zero

theorem x₂_neg (c : F) : cx₂ x₃ x₄ (-c) = (cx₂ x₃ x₄ c)⁻¹ := by
  have := h.x₂_add c (-c)
  rw [add_neg_cancel, h.x₂_zero] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem x₂_mem_P (c : F) : cx₂ x₃ x₄ c ∈ P := h.X₂_mem_P (h.θ_mem c)

theorem x₂_comm (c : F) (g : G) (hg : g ∈ P) : cx₂ x₃ x₄ c * g = g * cx₂ x₃ x₄ c :=
  h.cen₂ _ (h.θ_mem c) g hg

theorem c34' (a b : F) : x₃ a * x₄ b = cx₂ x₃ x₄ (a * b) * x₄ b * x₃ a := by
  have e := h.ω_eq_θ a b
  have : x₃ a * x₄ b = ⁅x₃ a, x₄ b⁆ * (x₄ b * x₃ a) := by simp only [commutatorElement_def]; group
  rw [this, e, mul_assoc]

theorem cm (u g : G) (c : F) (hg : g ∈ P) : u * g * cx₂ x₃ x₄ c = u * cx₂ x₃ x₄ c * g := by
  rw [mul_assoc u g, ← h.x₂_comm c g hg, ← mul_assoc]

theorem c34 (a b : F) : x₃ a * x₄ b = x₄ b * x₃ a * cx₂ x₃ x₄ (a * b) := by
  rw [h.c34' a b]
  have := h.cm 1 (x₄ b * x₃ a) (a * b) (P.mul_mem (h.x₄_mem_P b) (h.x₃_mem_P a))
  rw [one_mul, one_mul] at this
  rw [mul_assoc, ← this]

theorem x₄_x₃ (a b : F) : x₄ b * x₃ a = x₃ a * x₄ b * cx₂ x₃ x₄ (-(a * b)) := by
  have e := h.c34 a b
  rw [h.x₂_neg]
  have : x₄ b * x₃ a = x₃ a * x₄ b * (cx₂ x₃ x₄ (a * b))⁻¹ := by
    rw [e]; group
  exact this

theorem R2_mul (c a b c' a' b' : F) :
    (cx₂ x₃ x₄ c * x₃ a * x₄ b) * (cx₂ x₃ x₄ c' * x₃ a' * x₄ b') =
      cx₂ x₃ x₄ (c + c' - a' * b) * x₃ (a + a') * x₄ (b + b') := by
  have hx : x₄ b * x₃ a' = x₃ a' * x₄ b * cx₂ x₃ x₄ (-(a' * b)) := h.x₄_x₃ a' b
  have hsw : ∀ Q : G, Q * x₄ b * x₃ a' = Q * x₃ a' * x₄ b * cx₂ x₃ x₄ (-(a' * b)) := by
    intro Q
    rw [mul_assoc Q (x₄ b), hx]
    group
  rw [show (cx₂ x₃ x₄ c * x₃ a * x₄ b) * (cx₂ x₃ x₄ c' * x₃ a' * x₄ b') =
      cx₂ x₃ x₄ c * x₃ a * x₄ b * cx₂ x₃ x₄ c' * x₃ a' * x₄ b' by group]
  rw [h.cm (cx₂ x₃ x₄ c * x₃ a) (x₄ b) c' (h.x₄_mem_P b)]
  rw [h.cm (cx₂ x₃ x₄ c) (x₃ a) c' (h.x₃_mem_P a)]
  rw [hsw (cx₂ x₃ x₄ c * cx₂ x₃ x₄ c' * x₃ a)]
  rw [h.cm (cx₂ x₃ x₄ c * cx₂ x₃ x₄ c' * x₃ a * x₃ a') (x₄ b) (-(a' * b)) (h.x₄_mem_P b)]
  rw [h.cm (cx₂ x₃ x₄ c * cx₂ x₃ x₄ c' * x₃ a) (x₃ a') (-(a' * b)) (h.x₃_mem_P a')]
  rw [h.cm (cx₂ x₃ x₄ c * cx₂ x₃ x₄ c') (x₃ a) (-(a' * b)) (h.x₃_mem_P a)]
  rw [h.add₃, h.add₄, show c + c' - a' * b = c + c' + -(a' * b) by ring, h.x₂_add, h.x₂_add]
  group

theorem exists_f : ∃ f : F → F → F, ∀ s b,
    x₁ s * x₄ b * (x₁ s)⁻¹ = cx₂ x₃ x₄ (f s b) * x₃ (s * b) * x₄ b := by
  have : ∀ s b, ∃ c, x₁ s * x₄ b * (x₁ s)⁻¹ = cx₂ x₃ x₄ c * x₃ (s * b) * x₄ b := by
    intro s b
    obtain ⟨y, hy, e⟩ := h.u_X₄ s b
    obtain ⟨c, hc⟩ := h.θ_surj y hy
    refine ⟨c, ?_⟩
    rw [e, ← hc, h.cm (x₃ (s * b)) (x₄ b) c (h.x₄_mem_P b),
      ← h.x₂_comm c (x₃ (s * b)) (h.x₃_mem_P _)]
  choose f hf using this
  exact ⟨f, hf⟩

theorem f_eq [Finite F] (s b : F) :
    x₁ s * x₄ b * (x₁ s)⁻¹ = cx₂ x₃ x₄ (-(s * b ^ 2 / 2)) * x₃ (s * b) * x₄ b := by
  obtain ⟨f, hf⟩ := h.exists_f
  have inj := h.θ_inj
  have cancel : ∀ c c' a b : F, cx₂ x₃ x₄ c * x₃ a * x₄ b = cx₂ x₃ x₄ c' * x₃ a * x₄ b → c = c' := by
    intro c c' a b e
    apply inj
    exact mul_right_cancel (mul_right_cancel e)
  have c1 : ∀ s c : F, x₁ s * cx₂ x₃ x₄ c * (x₁ s)⁻¹ = cx₂ x₃ x₄ c := by
    intro s c
    rw [← h.x₂_comm c (x₁ s) (h.x₁_mem_P s)]
    group
  have c2 : ∀ s a : F, x₁ s * x₃ a * (x₁ s)⁻¹ = x₃ a := by
    intro s a
    rw [h.c13]
    group
  have hb : ∀ s b b', f s (b + b') = f s b + f s b' - s * b * b' := by
    intro s b b'
    have e2 : x₁ s * x₄ (b + b') * (x₁ s)⁻¹ =
        (x₁ s * x₄ b * (x₁ s)⁻¹) * (x₁ s * x₄ b' * (x₁ s)⁻¹) := by
      rw [h.add₄]; group
    rw [hf s (b + b'), hf s b, hf s b', h.R2_mul, mul_add] at e2
    have := cancel _ _ _ _ e2
    rw [this]
    ring
  have hs : ∀ s s' b, f (s + s') b = f s b + f s' b := by
    intro s s' b
    have e3 : x₁ (s + s') * x₄ b * (x₁ (s + s'))⁻¹ =
        x₁ s * (x₁ s' * x₄ b * (x₁ s')⁻¹) * (x₁ s)⁻¹ := by
      rw [h.add₁]; group
    have e3' : x₁ (s + s') * x₄ b * (x₁ (s + s'))⁻¹ =
        cx₂ x₃ x₄ (f s' b) * x₃ (s' * b) * (cx₂ x₃ x₄ (f s b) * x₃ (s * b) * x₄ b) := by
      rw [e3, hf s' b]
      calc x₁ s * (cx₂ x₃ x₄ (f s' b) * x₃ (s' * b) * x₄ b) * (x₁ s)⁻¹
          = (x₁ s * cx₂ x₃ x₄ (f s' b) * (x₁ s)⁻¹) * (x₁ s * x₃ (s' * b) * (x₁ s)⁻¹) *
              (x₁ s * x₄ b * (x₁ s)⁻¹) := by group
        _ = _ := by rw [c1, c2, hf s b]
    have e3'' : cx₂ x₃ x₄ (f s' b) * x₃ (s' * b) * (cx₂ x₃ x₄ (f s b) * x₃ (s * b) * x₄ b) =
        cx₂ x₃ x₄ (f s' b + f s b) * x₃ (s' * b + s * b) * x₄ b := by
      rw [h.x₂_add, h.add₃]
      calc cx₂ x₃ x₄ (f s' b) * x₃ (s' * b) * (cx₂ x₃ x₄ (f s b) * x₃ (s * b) * x₄ b)
          = cx₂ x₃ x₄ (f s' b) * x₃ (s' * b) * cx₂ x₃ x₄ (f s b) * x₃ (s * b) * x₄ b := by group
        _ = cx₂ x₃ x₄ (f s' b) * cx₂ x₃ x₄ (f s b) * x₃ (s' * b) * x₃ (s * b) * x₄ b := by
            rw [h.cm (cx₂ x₃ x₄ (f s' b)) (x₃ (s' * b)) (f s b) (h.x₃_mem_P _)]
        _ = _ := by group
    rw [hf (s + s') b, e3'', show (s + s') * b = s' * b + s * b by ring] at e3'
    have := cancel _ _ _ _ e3'
    rw [this]
    ring
  have ht : ∀ u : Fˣ, ∀ s b, f ((u : F) ^ 2 * s) ((u : F)⁻¹ * b) = f s b := by
    intro u s b
    have hu : (u : F) ≠ 0 := u.ne_zero
    have e4 := congrArg (fun g => dg u * g * (dg u)⁻¹) (hf s b)
    have l : dg u * (x₁ s * x₄ b * (x₁ s)⁻¹) * (dg u)⁻¹ =
        x₁ ((u : F) ^ 2 * s) * x₄ ((u : F)⁻¹ * b) * (x₁ ((u : F) ^ 2 * s))⁻¹ := by
      rw [← h.dg_X₁ u s, ← h.dg_X₄ u b]
      group
    have r : dg u * (cx₂ x₃ x₄ (f s b) * x₃ (s * b) * x₄ b) * (dg u)⁻¹ =
        cx₂ x₃ x₄ (f s b) * x₃ ((u : F) ^ 2 * s * ((u : F)⁻¹ * b)) * x₄ ((u : F)⁻¹ * b) := by
      have hz : dg u * cx₂ x₃ x₄ (f s b) * (dg u)⁻¹ = cx₂ x₃ x₄ (f s b) := by
        rw [h.dg_X₂ u _ (h.θ_mem (f s b))]; group
      have e5 : (u : F) ^ 2 * s * ((u : F)⁻¹ * b) = (u : F) * (s * b) := by
        field_simp
      calc dg u * (cx₂ x₃ x₄ (f s b) * x₃ (s * b) * x₄ b) * (dg u)⁻¹
          = (dg u * cx₂ x₃ x₄ (f s b) * (dg u)⁻¹) * (dg u * x₃ (s * b) * (dg u)⁻¹) *
              (dg u * x₄ b * (dg u)⁻¹) := by group
        _ = cx₂ x₃ x₄ (f s b) * x₃ ((u : F) ^ 2 * s * ((u : F)⁻¹ * b)) * x₄ ((u : F)⁻¹ * b) := by
            rw [hz, h.dg_X₃, h.dg_X₄, e5]
    rw [l, r] at e4
    rw [hf ((u : F) ^ 2 * s) ((u : F)⁻¹ * b)] at e4
    exact cancel _ _ _ _ e4
  have key := quad_term_eq h.two_ne f
    hb hs ht s b
  rw [hf s b, key]

theorem c14 [Finite F] (s b : F) :
    x₁ s * x₄ b = x₄ b * x₃ (s * b) * cx₂ x₃ x₄ (s * b ^ 2 / 2) * x₁ s := by
  have e := h.f_eq s b
  have e1 : x₁ s * x₄ b = cx₂ x₃ x₄ (-(s * b ^ 2 / 2)) * x₃ (s * b) * x₄ b * x₁ s := by
    have := congrArg (fun g => g * x₁ s) e
    simp only [inv_mul_cancel_right] at this
    exact this
  rw [e1]
  have hx : x₄ b * x₃ (s * b) = x₃ (s * b) * x₄ b * cx₂ x₃ x₄ (-(s * b * b)) := h.x₄_x₃ (s * b) b
  have e2 : x₄ b * x₃ (s * b) * cx₂ x₃ x₄ (s * b ^ 2 / 2) =
      cx₂ x₃ x₄ (-(s * b ^ 2 / 2)) * x₃ (s * b) * x₄ b := by
    rw [hx]
    have hq : -(s * b * b) + s * b ^ 2 / 2 = -(s * b ^ 2 / 2) := by
      have := h.two_ne
      field_simp
      ring
    calc x₃ (s * b) * x₄ b * cx₂ x₃ x₄ (-(s * b * b)) * cx₂ x₃ x₄ (s * b ^ 2 / 2)
        = x₃ (s * b) * x₄ b * (cx₂ x₃ x₄ (-(s * b * b)) * cx₂ x₃ x₄ (s * b ^ 2 / 2)) := by group
      _ = x₃ (s * b) * x₄ b * cx₂ x₃ x₄ (-(s * b ^ 2 / 2)) := by rw [← h.x₂_add, hq]
      _ = cx₂ x₃ x₄ (-(s * b ^ 2 / 2)) * x₃ (s * b) * x₄ b := by
          rw [h.cm (x₃ (s * b)) (x₄ b) _ (h.x₄_mem_P b),
            ← h.x₂_comm _ (x₃ (s * b)) (h.x₃_mem_P _)]
  rw [e2]

theorem exists_coord [Finite F] :
    ∃ (x₂ : F → G) (hx₂ : ∀ c, x₂ c ∈ P), (∀ g, g ∈ X₂ ↔ ∃ c, x₂ c = g) ∧
      SPLCoord (fun s => (⟨x₁ s, h.x₁_mem_P s⟩ : ↥P)) (fun c => (⟨x₂ c, hx₂ c⟩ : ↥P))
        (fun a => (⟨x₃ a, h.x₃_mem_P a⟩ : ↥P)) (fun b => (⟨x₄ b, h.x₄_mem_P b⟩ : ↥P)) := by
  classical
  refine ⟨cx₂ x₃ x₄, h.x₂_mem_P, ?_, ?_⟩
  · intro g
    constructor
    · intro hg
      obtain ⟨c, hc⟩ := h.θ_surj g hg
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      exact h.θ_mem c
  · have hsurj : ∀ g : ↥P, ∃ s c a b : F, g = ⟨x₁ s, h.x₁_mem_P s⟩ * ⟨cx₂ x₃ x₄ c, h.x₂_mem_P c⟩ *
        ⟨x₃ a, h.x₃_mem_P a⟩ * ⟨x₄ b, h.x₄_mem_P b⟩ := by
      intro g
      obtain ⟨s, r, hr, hgr⟩ := h.fac_P g.1 g.2
      obtain ⟨y, hy, a, b, hrr⟩ := h.fac₂ r hr
      obtain ⟨c, hc⟩ := h.θ_surj y hy
      refine ⟨s, c, a, b, Subtype.ext ?_⟩
      show (g : G) = x₁ s * cx₂ x₃ x₄ c * x₃ a * x₄ b
      rw [hgr, hrr, ← hc]
      group
    have hinj : ∀ s c a b s' c' a' b' : F,
        (⟨x₁ s, h.x₁_mem_P s⟩ * ⟨cx₂ x₃ x₄ c, h.x₂_mem_P c⟩ * ⟨x₃ a, h.x₃_mem_P a⟩ *
          ⟨x₄ b, h.x₄_mem_P b⟩ : ↥P) =
        ⟨x₁ s', h.x₁_mem_P s'⟩ * ⟨cx₂ x₃ x₄ c', h.x₂_mem_P c'⟩ * ⟨x₃ a', h.x₃_mem_P a'⟩ *
          ⟨x₄ b', h.x₄_mem_P b'⟩ → s = s' ∧ c = c' ∧ a = a' ∧ b = b' := by
      let Ψ : F × F × F × F → ↥P := fun v =>
        ⟨x₁ v.1, h.x₁_mem_P v.1⟩ * ⟨cx₂ x₃ x₄ v.2.1, h.x₂_mem_P v.2.1⟩ *
          ⟨x₃ v.2.2.1, h.x₃_mem_P v.2.2.1⟩ * ⟨x₄ v.2.2.2, h.x₄_mem_P v.2.2.2⟩
      have hΨs : Function.Surjective Ψ := by
        intro g
        obtain ⟨s, c, a, b, hg⟩ := hsurj g
        exact ⟨(s, c, a, b), hg.symm⟩
      have hcard : Nat.card (F × F × F × F) = Nat.card ↥P := by
        rw [h.cardP, Nat.card_prod, Nat.card_prod, Nat.card_prod, h.card_F]
        ring
      have hFpos : 0 < Nat.card F := Nat.card_pos
      have : Finite ↥P := Nat.finite_of_card_ne_zero (by
        rw [h.cardP, ← h.card_F]; exact (pow_pos hFpos 4).ne')
      have hΨ : Function.Injective Ψ := hΨs.injective_of_finite (Finite.card_eq.mp hcard).some
      intro s c a b s' c' a' b' he
      have := hΨ (a₁ := (s, c, a, b)) (a₂ := (s', c', a', b')) he
      simp only [Prod.mk.injEq] at this
      exact this
    refine
      { add₁ := fun s s' => Subtype.ext (h.add₁ s s')
        add₂ := fun c c' => Subtype.ext (h.x₂_add c c')
        add₃ := fun a a' => Subtype.ext (h.add₃ a a')
        add₄ := fun b b' => Subtype.ext (h.add₄ b b')
        surj := hsurj
        inj := hinj
        cen₂ := fun c g => Subtype.ext (h.x₂_comm c g.1 g.2)
        c13 := fun s a => Subtype.ext (h.c13 s a)
        c34 := fun a b => Subtype.ext (h.c34 a b)
        c14 := fun s b => Subtype.ext (h.c14 s b) }

end SPLGData

end CFSG.GH74.GLS.SP.Local
