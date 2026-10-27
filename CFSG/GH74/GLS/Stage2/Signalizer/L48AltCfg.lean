module

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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Equiv Equiv.Perm Subgroup

abbrev Z2Cube : Type := Fin 3 → Multiplicative (ZMod 2)

theorem z2Cube_sq (m : Z2Cube) : m * m = 1 := by
  funext i
  have : ∀ a : Multiplicative (ZMod 2), a * a = 1 := by decide
  exact this _

theorem z2Cube_card : Fintype.card Z2Cube = 8 := by
  simp [Fintype.card_pi, ZMod.card]

@[expose] noncomputable def z2Reg : Z2Cube →* Perm Z2Cube := MulAction.toPermHom Z2Cube Z2Cube

theorem z2Reg_apply (a x : Z2Cube) : z2Reg a x = a * x := rfl

theorem z2Reg_injective : Function.Injective z2Reg := by
  intro a b h
  have := congrArg (fun σ => σ 1) h
  simpa [z2Reg_apply] using this

theorem z2Reg_cycleType {a : Z2Cube} (ha : a ≠ 1) : (z2Reg a).cycleType = {2, 2, 2, 2} := by
  have hsq : (z2Reg a) ^ 2 = 1 := by
    rw [← map_pow, pow_two, z2Cube_sq, map_one]
  have hne : z2Reg a ≠ 1 := fun h => ha (z2Reg_injective (by rw [h, map_one]))
  have hord : orderOf (z2Reg a) = 2 := orderOf_eq_prime hsq hne
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (σ := z2Reg a) (by rw [hord]; exact Nat.prime_two)
  have hsupp : (z2Reg a).support = Finset.univ := by
    ext x
    simp only [Perm.mem_support, Finset.mem_univ, iff_true, z2Reg_apply]
    intro h
    apply ha
    have := congrArg (fun y => y * x⁻¹) h
    simpa using this
  have hsum := Perm.sum_cycleType (z2Reg a)
  rw [hk, hsupp, hord, Multiset.sum_replicate, smul_eq_mul, Finset.card_univ] at hsum
  have hk3 : k = 3 := by
    have := z2Cube_card
    omega
  rw [hk, hk3, hord]
  rfl

theorem cycleType_viaEmbeddingHom {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (ι : α ↪ β) (σ : Perm α) :
    (Equiv.Perm.viaEmbeddingHom ι σ).cycleType = σ.cycleType := by
  show (Equiv.Perm.viaEmbedding σ ι).cycleType = σ.cycleType
  unfold Equiv.Perm.viaEmbedding
  classical
  convert Equiv.Perm.cycleType_extendDomain (Equiv.ofInjective ι.1 ι.2) (g := σ) using 3

theorem sign_eq_one_of_cycleType_two_four {n : ℕ} {σ : Perm (Fin n)}
    (h : σ.cycleType = {2, 2, 2, 2}) : Perm.sign σ = 1 := by
  rw [Perm.sign_of_cycleType, h]
  decide

structure AltConfig (n : ℕ) (R : Subgroup (Perm (Fin n))) (B : Set (Fin n)) : Prop where
  card_B : Nat.card ↥B = 8
  cyc : ∀ ρ ∈ R, ρ ≠ 1 → ρ.cycleType = {2, 2, 2, 2}
  supp : ∀ ρ ∈ R, ρ ≠ 1 → ∀ x, ρ x ≠ x ↔ x ∈ B
  trans : ∀ b ∈ B, ∀ b' ∈ B, ∃ ρ ∈ R, ρ b = b'
  card_R : 8 ≤ Nat.card ↥R

theorem exists_altConfig {n : ℕ} (hn : 8 ≤ n) : ∃ (R : Subgroup (Perm (Fin n))) (B : Set (Fin n)), AltConfig n R B := by
  classical
  obtain ⟨ι⟩ : Nonempty (Z2Cube ↪ Fin n) := Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin, z2Cube_card]
    exact hn)
  let θ : Z2Cube →* Perm (Fin n) := (Equiv.Perm.viaEmbeddingHom ι).comp z2Reg
  have hθinj : Function.Injective θ :=
    (Equiv.Perm.viaEmbeddingHom_injective ι).comp z2Reg_injective
  have hθ_apply : ∀ (a x : Z2Cube), θ a (ι x) = ι (a * x) := fun a x => by
    show Equiv.Perm.viaEmbedding (z2Reg a) ι (ι x) = _
    rw [Equiv.Perm.viaEmbedding_apply]
    rfl
  have hθ_out : ∀ (a : Z2Cube) (y : Fin n), y ∉ Set.range ι → θ a y = y := fun a y hy => by
    show Equiv.Perm.viaEmbedding (z2Reg a) ι y = _
    exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ y hy
  refine ⟨θ.range, Set.range ι, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_range_of_injective ι.injective, Nat.card_eq_fintype_card, z2Cube_card]
  · rintro _ ⟨a, rfl⟩ hne
    have ha : a ≠ 1 := fun h => hne (by rw [h, map_one])
    show (Equiv.Perm.viaEmbeddingHom ι (z2Reg a)).cycleType = _
    rw [cycleType_viaEmbeddingHom, z2Reg_cycleType ha]
  · rintro _ ⟨a, rfl⟩ hne x
    have ha : a ≠ 1 := fun h => hne (by rw [h, map_one])
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨y, rfl⟩ := hx
      rw [hθ_apply]
      simp only [Set.mem_range, exists_apply_eq_apply, iff_true]
      intro h
      apply ha
      have := ι.injective h
      have h2 := congrArg (fun w => w * y⁻¹) this
      simpa using h2
    · rw [hθ_out a x hx]
      simp [hx]
  · rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
    refine ⟨θ (x' * x⁻¹), ⟨_, rfl⟩, ?_⟩
    rw [hθ_apply]
    exact congrArg ι (inv_mul_cancel_right x' x)
  · calc 8 = Nat.card Z2Cube := by rw [Nat.card_eq_fintype_card, z2Cube_card]
      _ = Nat.card θ.range := Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv
      _ ≤ _ := le_rfl


theorem AltConfig.mem_alt {n : ℕ} {R : Subgroup (Perm (Fin n))} {B : Set (Fin n)} (hc : AltConfig n R B)
    {ρ : Perm (Fin n)} (hρ : ρ ∈ R) : ρ ∈ alternatingGroup (Fin n) := by
  by_cases h1 : ρ = 1
  · rw [h1]; exact one_mem _
  · exact Perm.mem_alternatingGroup.mpr (sign_eq_one_of_cycleType_two_four (hc.cyc ρ hρ h1))


end CFSG.GH74.GLS.Stage2.Signalizer.L48
