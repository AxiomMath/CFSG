module

public import Mathlib.Algebra.Group.Equiv.Finite
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
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped commutatorElement

abbrev V4 : Type := Multiplicative (ZMod 2 × ZMod 2)

section Standard

theorem v4_card_mulAut : Nat.card (MulAut V4) = 6 := by
  classical
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem v4_invol_fixed : ∀ σ : MulAut V4, σ ≠ 1 → σ * σ = 1 →
    Fintype.card {u : V4 // σ u = u} = 2 := by decide +kernel

theorem v4_three_fixed : ∀ σ : MulAut V4, σ ≠ 1 → σ ^ 3 = 1 → ∀ u : V4, σ u = u → u = 1 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem v4_cubes : ∀ σ τ : MulAut V4, σ ^ 3 = 1 → τ ^ 3 = 1 → (σ * τ) ^ 3 = 1 := by
  decide +kernel

theorem v4_sq_cube : ∀ σ : MulAut V4, (σ ^ 2) ^ 3 = 1 := by decide +kernel

theorem v4_card_cube : Fintype.card {σ : MulAut V4 // σ ^ 3 = 1} = 3 := by decide +kernel

end Standard

section Plane

variable {U : Type*} [Group U] [IsKleinFour U]

noncomputable def planeEquiv (U : Type*) [Group U] [IsKleinFour U] : U ≃* V4 :=
  (IsKleinFour.nonempty_mulEquiv (G₁ := U) (G₂ := V4)).some

theorem planeEquiv_congr (σ : MulAut U) (u : U) :
    (MulAut.congr (planeEquiv U) σ) (planeEquiv U u) = planeEquiv U (σ u) := by
  simp [MulAut.congr_apply]

theorem card_mulAut : Nat.card (MulAut U) = 6 := by
  rw [Nat.card_congr (MulAut.congr (planeEquiv U)).toEquiv]
  exact v4_card_mulAut

instance finite_mulAut : Finite (MulAut U) :=
  Nat.finite_of_card_ne_zero (by rw [card_mulAut]; norm_num)

theorem card_le_two_of_isPGroup {X : Subgroup (MulAut U)} (hX : IsPGroup 2 X) :
    Nat.card X ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hdvd : Nat.card X ∣ 6 := card_mulAut (U := U) ▸ Subgroup.card_subgroup_dvd_card X
  rw [hn] at hdvd ⊢
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · exfalso
    have h4 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 h
    have := h4.trans hdvd
    norm_num at this

theorem card_fixed_of_invol {σ : MulAut U} (h1 : σ ≠ 1) (h2 : σ * σ = 1) :
    Nat.card {u : U // σ u = u} = 2 := by
  classical
  set e := planeEquiv U
  set σ' := MulAut.congr e σ with hσ'
  have h1' : σ' ≠ 1 := fun h => h1 (by
    have := (MulAut.congr e).injective (h.trans (map_one _).symm)
    exact this)
  have h2' : σ' * σ' = 1 := by
    rw [hσ', ← map_mul, h2, map_one]
  have key := v4_invol_fixed σ' h1' h2'
  rw [← key, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun u => ?_)
  rw [hσ']
  have := planeEquiv_congr σ u
  constructor
  · intro h
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    rw [this, h]
  · intro h
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe] at h
    rw [this] at h
    exact e.injective h

theorem eq_one_of_fixed_of_pow_three {σ : MulAut U} (h1 : σ ≠ 1) (h3 : σ ^ 3 = 1) {u : U}
    (hu : σ u = u) : u = 1 := by
  set e := planeEquiv U
  set σ' := MulAut.congr e σ with hσ'
  have h1' : σ' ≠ 1 := fun h => h1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have h3' : σ' ^ 3 = 1 := by rw [hσ', ← map_pow, h3, map_one]
  have hu' : σ' (e u) = e u := by rw [planeEquiv_congr, hu]
  have := v4_three_fixed σ' h1' h3' (e u) hu'
  exact e.injective (by rw [this, map_one])

theorem pow_three_mul {σ τ : MulAut U} (h1 : σ ^ 3 = 1) (h2 : τ ^ 3 = 1) : (σ * τ) ^ 3 = 1 := by
  set e := planeEquiv U
  have := v4_cubes (MulAut.congr e σ) (MulAut.congr e τ) (by rw [← map_pow, h1, map_one])
    (by rw [← map_pow, h2, map_one])
  have h : MulAut.congr e ((σ * τ) ^ 3) = 1 := by rw [map_pow, map_mul]; exact this
  exact (MulAut.congr e).injective (h.trans (map_one _).symm)

theorem pow_two_pow_three (σ : MulAut U) : (σ ^ 2) ^ 3 = 1 := by
  set e := planeEquiv U
  have := v4_sq_cube (MulAut.congr e σ)
  have h : MulAut.congr e ((σ ^ 2) ^ 3) = 1 := by rw [map_pow, map_pow]; exact this
  exact (MulAut.congr e).injective (h.trans (map_one _).symm)

@[expose] def cubeSubgroup (U : Type*) [Group U] [IsKleinFour U] : Subgroup (MulAut U) where
  carrier := {σ | σ ^ 3 = 1}
  one_mem' := one_pow 3
  mul_mem' := fun {σ τ} h1 h2 => pow_three_mul h1 h2
  inv_mem' := fun {σ} h => by
    show σ⁻¹ ^ 3 = 1
    rw [inv_pow]
    have : σ ^ 3 = 1 := h
    rw [this, inv_one]

theorem mem_cubeSubgroup {σ : MulAut U} : σ ∈ cubeSubgroup U ↔ σ ^ 3 = 1 := Iff.rfl

instance cubeSubgroup_normal : (cubeSubgroup U).Normal :=
  ⟨fun σ hσ g => by
    show (g * σ * g⁻¹) ^ 3 = 1
    rw [conj_pow]
    have : σ ^ 3 = 1 := hσ
    rw [this]
    simp⟩

theorem card_cubeSubgroup : Nat.card (cubeSubgroup U) = 3 := by
  classical
  set e := planeEquiv U
  have hv : Nat.card {σ : MulAut V4 // σ ^ 3 = 1} = 3 := by
    rw [Nat.card_eq_fintype_card]; exact v4_card_cube
  rw [← hv]
  refine Nat.card_congr ?_
  refine Equiv.subtypeEquiv (MulAut.congr e).toEquiv fun σ => ?_
  constructor
  · intro h
    show (MulAut.congr e σ) ^ 3 = 1
    rw [← map_pow]
    have : σ ^ 3 = 1 := h
    rw [this, map_one]
  · intro h
    show σ ^ 3 = 1
    have h' : (MulAut.congr e σ) ^ 3 = 1 := h
    rw [← map_pow] at h'
    exact (MulAut.congr e).injective (h'.trans (map_one _).symm)

end Plane

end CFSG.QuasithinUnique.Setup.Wreath
