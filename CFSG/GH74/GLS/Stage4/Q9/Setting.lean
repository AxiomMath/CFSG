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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup Matrix

structure Q9Setting (G : Type) [Group G] (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] where
  z_ord : orderOf z = 2
  one_class : ∀ u : G, orderOf u = 2 → IsConj z u
  card₁ : Nat.card F₁ = 9
  card₂ : Nat.card F₂ = 9
  φ₁ : K₁ ≃* SpecialLinearGroup (Fin 2) F₁
  φ₂ : K₂ ≃* SpecialLinearGroup (Fin 2) F₂
  le_centralizer₁ : K₁ ≤ centralizer ({z} : Set G)
  le_centralizer₂ : K₂ ≤ centralizer ({z} : Set G)
  normal₁ : ∀ c ∈ centralizer ({z} : Set G), ∀ k ∈ K₁, c * k * c⁻¹ ∈ K₁
  normal₂ : ∀ c ∈ centralizer ({z} : Set G), ∀ k ∈ K₂, c * k * c⁻¹ ∈ K₂
  comm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x
  inter_eq : K₁ ⊓ K₂ = zpowers z
  index_two : (K₁ ⊔ K₂).relIndex (centralizer ({z} : Set G)) = 2
  card3 : (Nat.card G).factorization 3 = (Nat.card (centralizer ({z} : Set G))).factorization 3
  card2 : (Nat.card G).factorization 2 = (Nat.card (centralizer ({z} : Set G))).factorization 2
  t : G
  t_ord : orderOf t = 2
  t_mem : t ∈ centralizer ({z} : Set G)
  t_notin : t ∉ K₁ ⊔ K₂
  A : GeneralLinearGroup (Fin 2) F₁
  B : GeneralLinearGroup (Fin 2) F₂
  A_act : ∀ k k' : K₁, (k' : G) = t * k * t⁻¹ →
    ((φ₁ k' : SpecialLinearGroup (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁) =
      (A : Matrix (Fin 2) (Fin 2) F₁) * (φ₁ k : Matrix (Fin 2) (Fin 2) F₁) *
        ((A⁻¹ : GeneralLinearGroup (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁)
  B_act : ∀ k k' : K₂, (k' : G) = t * k * t⁻¹ →
    ((φ₂ k' : SpecialLinearGroup (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) =
      (B : Matrix (Fin 2) (Fin 2) F₂) * (φ₂ k : Matrix (Fin 2) (Fin 2) F₂) *
        ((B⁻¹ : GeneralLinearGroup (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂)
  A_det : ¬ IsSquare (Matrix.det (A : Matrix (Fin 2) (Fin 2) F₁))
  B_det : ¬ IsSquare (Matrix.det (B : Matrix (Fin 2) (Fin 2) F₂))
  Hs : Subgroup G
  Hs_iso : Nonempty (↥Hs ≃* Multiplicative (ZMod 10) × Multiplicative (ZMod 10))
  Hs_le : Hs ≤ centralizer ((closure ({z, t} : Set G) : Subgroup G) : Set G)
  Hs_ge₁ : K₁ ⊓ centralizer ((closure ({z, t} : Set G) : Subgroup G) : Set G) ≤ Hs
  Hs_ge₂ : K₂ ⊓ centralizer ((closure ({z, t} : Set G) : Subgroup G) : Set G) ≤ Hs
  normalizer_eq : normalizer ((closure ({z, t} : Set G) : Subgroup G) : Set G) = normalizer (Hs : Set G)
  tns : ∀ n ∈ normalizer (Hs : Set G), orderOf n = 3 → ∀ h ∈ Hs, h ≠ 1 → n * h * n⁻¹ ≠ h
  as : G
  as_ord : orderOf as = 3
  as_mem : as ∈ normalizer (Hs : Set G)
  as_moves : as * z * as⁻¹ ≠ z
  u : G
  u_mem : u ∈ K₁ ⊔ K₂
  u_ord : orderOf u = 2
  u_ne : u ≠ z
  w₁ : G
  w₂ : G
  w₁_mem : w₁ ∈ K₁
  w₂_mem : w₂ ∈ K₂
  w₁_sq : w₁ * w₁ = z
  w₂_sq : w₂ * w₂ = z
  w₁_act : w₁ * u * w₁⁻¹ = u * z
  w₂_act : w₂ * u * w₂⁻¹ = u * z
  a : G
  a_norm_z : a * z * a⁻¹ ∈ closure ({z, u} : Set G)
  a_norm_u : a * u * a⁻¹ ∈ closure ({z, u} : Set G)
  a_moves : a * z * a⁻¹ ≠ z
  a_cent : a * (w₁ * w₂) * a⁻¹ = w₁ * w₂

end CFSG.GH74.GLS.Stage4.Q9
