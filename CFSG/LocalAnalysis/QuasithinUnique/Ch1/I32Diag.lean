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

namespace CFSG.QuasithinUnique.I32

open Subgroup
open scoped commutatorElement

variable {Y : Type*} [Group Y]

@[expose] def tau (σ : Y ≃* Y) (K : Subgroup Y)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * σ b = σ b * a) : ↥K →* Y where
  toFun a := (a : Y) * σ (a : Y)
  map_one' := by simp
  map_mul' a b := by
    have h : (b : Y) * σ a = σ a * b := hcomm b b.2 a a.2
    simp only [Subgroup.coe_mul, map_mul]
    calc (a : Y) * b * (σ a * σ b) = a * (b * σ a) * σ b := by group
      _ = a * (σ a * b) * σ b := by rw [h]
      _ = _ := by group

theorem tau_apply (σ : Y ≃* Y) (K : Subgroup Y)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * σ b = σ b * a) (a : K) :
    tau σ K hcomm a = (a : Y) * σ (a : Y) := rfl

theorem le_normalizer_map (σ : Y ≃* Y) (K : Subgroup Y)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * σ b = σ b * a) :
    K ≤ normalizer ((K.map σ.toMonoidHom : Subgroup Y) : Set Y) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    change σ b = a * σ b * a⁻¹
    rw [hcomm a ha b hb]; group
  · rintro ⟨b, hb, hbe⟩
    refine ⟨b, hb, ?_⟩
    change σ b = a * y * a⁻¹ at hbe
    have h1 : y = a⁻¹ * σ b * a := by rw [hbe]; group
    have h2 := hcomm a ha b hb
    change σ b = y
    rw [h1]
    calc σ b = a⁻¹ * (a * σ b) := by group
      _ = a⁻¹ * (σ b * a) := by rw [h2]
      _ = a⁻¹ * σ b * a := by group

theorem exists_decomp (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y) (K : Subgroup Y)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * σ b = σ b * a)
    {x : Y} (hx : x ∈ K ⊔ K.map σ.toMonoidHom) (hfix : σ x = x) :
    ∃ a ∈ K, ∃ z ∈ K ⊓ K.map σ.toMonoidHom, x = a * σ a * z := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right K (K.map σ.toMonoidHom)
    (le_normalizer_map σ K hcomm)
  have hx' : x ∈ (↑(K ⊔ K.map σ.toMonoidHom) : Set Y) := hx
  rw [hset] at hx'
  obtain ⟨a, ha, b', hb', rfl⟩ := hx'
  obtain ⟨b₀, hb₀, rfl⟩ := hb'
  have hfix' : σ (a * σ b₀) = a * σ b₀ := hfix
  rw [map_mul, hσ] at hfix'
  have hc : b₀ * σ a = σ a * b₀ := hcomm b₀ hb₀ a ha
  have hu : a⁻¹ * b₀ = σ (b₀ * a⁻¹) := by
    rw [map_mul, map_inv]
    calc a⁻¹ * b₀ = a⁻¹ * (b₀ * σ a) * (σ a)⁻¹ := by group
      _ = a⁻¹ * (σ a * b₀) * (σ a)⁻¹ := by rw [hc]
      _ = σ b₀ * (σ a)⁻¹ := by rw [hfix']; group
  have huK : a⁻¹ * b₀ ∈ K := K.mul_mem (K.inv_mem ha) hb₀
  have huK' : a⁻¹ * b₀ ∈ K.map σ.toMonoidHom := by
    rw [hu]
    exact ⟨b₀ * a⁻¹, K.mul_mem hb₀ (K.inv_mem ha), rfl⟩
  refine ⟨a, ha, σ (a⁻¹ * b₀), ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨w, hw, hwe⟩ := huK'
    have : σ (a⁻¹ * b₀) = w := by
      rw [← hwe]; exact hσ w
    rw [this]; exact hw
  · exact ⟨a⁻¹ * b₀, huK, rfl⟩
  · have : b₀ = a * (a⁻¹ * b₀) := by group
    calc a * σ b₀ = a * σ (a * (a⁻¹ * b₀)) := by rw [← this]
      _ = a * σ a * σ (a⁻¹ * b₀) := by rw [map_mul]; group

theorem commutatorElement_mul_mul_of_commute {x y u w : Y} (hu : Commute u y) (hw : Commute x w)
    (huw : Commute u w) : ⁅x * u, y * w⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, (hw.mul_left huw).commutator_eq,
    commutatorElement_mul_left_eq_conj_mul, hu.commutator_eq]
  group

theorem commute_of_mem_inf (σ : Y ≃* Y) (K : Subgroup Y)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * σ b = σ b * a)
    {z : Y} (hz : z ∈ K ⊓ K.map σ.toMonoidHom) {x : Y} (hx : x ∈ K ⊔ K.map σ.toMonoidHom) :
    Commute z x := by
  have hK : K.map σ.toMonoidHom ≤ centralizer (K : Set Y) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_iff]
    intro a ha
    exact hcomm a ha b hb
  have hσK : K ≤ centralizer ((K.map σ.toMonoidHom : Subgroup Y) : Set Y) := by
    intro a ha
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact (hcomm a ha b hb).symm
  have hsup : K ⊔ K.map σ.toMonoidHom ≤ centralizer ({z} : Set Y) := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (hK hz.2) a ha)
    · intro b hb
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (hσK hz.1) b hb)
  exact (mem_centralizer_singleton_iff.mp (hsup hx)).symm

theorem commutator_le_range (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y) (K : Subgroup Y)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * σ b = σ b * a) (C : Subgroup Y)
    (hC : ∀ x ∈ C, σ x = x) :
    ⁅(K ⊔ K.map σ.toMonoidHom) ⊓ C, (K ⊔ K.map σ.toMonoidHom) ⊓ C⁆ ≤
      (tau σ K hcomm).range := by
  rw [Subgroup.commutator_le]
  rintro x ⟨hxA, hxC⟩ y ⟨hyA, hyC⟩
  obtain ⟨a, ha, z, hz, rfl⟩ := exists_decomp σ hσ K hcomm hxA (hC x hxC)
  obtain ⟨a', ha', z', hz', rfl⟩ := exists_decomp σ hσ K hcomm hyA (hC y hyC)
  have hpA : a * σ a ∈ K ⊔ K.map σ.toMonoidHom :=
    mul_mem (mem_sup_left ha) (mem_sup_right ⟨a, ha, rfl⟩)
  have hqA : a' * σ a' ∈ K ⊔ K.map σ.toMonoidHom :=
    mul_mem (mem_sup_left ha') (mem_sup_right ⟨a', ha', rfl⟩)
  have hz'A : z' ∈ K ⊔ K.map σ.toMonoidHom := mem_sup_left hz'.1
  rw [commutatorElement_mul_mul_of_commute
    (commute_of_mem_inf σ K hcomm hz hqA) ((commute_of_mem_inf σ K hcomm hz' hpA).symm)
    (commute_of_mem_inf σ K hcomm hz hz'A)]
  refine ⟨⁅(⟨a, ha⟩ : K), (⟨a', ha'⟩ : K)⁆, ?_⟩
  rw [map_commutatorElement]
  rfl

theorem tau_fixed (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y) (K : Subgroup Y)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * σ b = σ b * a) (a : K) :
    σ (tau σ K hcomm a) = tau σ K hcomm a := by
  rw [tau_apply, map_mul, hσ]
  exact (hcomm a a.2 a a.2).symm

theorem mem_map_of_tau_eq_one (σ : Y ≃* Y) (K : Subgroup Y)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * σ b = σ b * a) {a : K} (h : tau σ K hcomm a = 1) :
    (a : Y) ∈ K.map σ.toMonoidHom := by
  rw [tau_apply] at h
  have h1 : (a : Y) = (σ (a : Y))⁻¹ := eq_inv_of_mul_eq_one_left h
  have h3 : σ (a : Y) ∈ K.map σ.toMonoidHom := ⟨a, a.2, rfl⟩
  rw [h1]
  exact inv_mem h3

end CFSG.QuasithinUnique.I32
