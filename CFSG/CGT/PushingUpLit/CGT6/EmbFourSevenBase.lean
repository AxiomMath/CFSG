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

namespace CFSG.CGT.PushingUpLit.CGT6

variable {V : Type*} [CommGroup V]

@[expose] def centKer (Y X : Subgroup (MulAut V)) : Subgroup ↥Y where
  carrier := {y | ∀ x ∈ X, (y : MulAut V) * x = x * (y : MulAut V)}
  one_mem' := fun x _ => by simp
  mul_mem' := fun {a b} ha hb x hx => by
    show ((a : MulAut V) * (b : MulAut V)) * x = x * ((a : MulAut V) * (b : MulAut V))
    rw [mul_assoc, hb x hx, ← mul_assoc, ha x hx, mul_assoc]
  inv_mem' := fun {a} ha x hx => by
    show (a : MulAut V)⁻¹ * x = x * (a : MulAut V)⁻¹
    exact (Commute.inv_left (show Commute (a : MulAut V) x from ha x hx)).eq

theorem centKer_normal {Y X : Subgroup (MulAut V)}
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) : (centKer Y X).Normal where
  conj_mem k hk g x hx := by
    have hx' : (g : MulAut V)⁻¹ * x * (g : MulAut V) ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hYX (Y.inv_mem g.2)) x).mp hx
      simpa using this
    have h1 := hk _ hx'
    show ((g : MulAut V) * (k : MulAut V) * (g : MulAut V)⁻¹) * x =
      x * ((g : MulAut V) * (k : MulAut V) * (g : MulAut V)⁻¹)
    calc (g : MulAut V) * (k : MulAut V) * (g : MulAut V)⁻¹ * x
        = (g : MulAut V) * ((k : MulAut V) * ((g : MulAut V)⁻¹ * x * (g : MulAut V))) *
            (g : MulAut V)⁻¹ := by group
      _ = (g : MulAut V) * (((g : MulAut V)⁻¹ * x * (g : MulAut V)) * (k : MulAut V)) *
            (g : MulAut V)⁻¹ := by rw [h1]
      _ = x * ((g : MulAut V) * (k : MulAut V) * (g : MulAut V)⁻¹) := by group

theorem le_centralizer_of_centKer_eq_top {Y X : Subgroup (MulAut V)} (h : centKer Y X = ⊤) :
    X ≤ Subgroup.centralizer (Y : Set (MulAut V)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have : (⟨y, hy⟩ : ↥Y) ∈ centKer Y X := by rw [h]; trivial
  exact this x hx

theorem mem_centKer_of_le_centralizer {Y X : Subgroup (MulAut V)} {e : MulAut V} (heY : e ∈ Y)
    (h : X ≤ Subgroup.centralizer ({e} : Set (MulAut V))) : (⟨e, heY⟩ : ↥Y) ∈ centKer Y X :=
  fun _ hx => Subgroup.mem_centralizer_iff.mp (h hx) e rfl

theorem centKer_eq_top_of_simple {Y X : Subgroup (MulAut V)} [IsSimpleGroup ↥Y]
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) {e : MulAut V} (heY : e ∈ Y)
    (he1 : e ≠ 1) (h : X ≤ Subgroup.centralizer ({e} : Set (MulAut V))) : centKer Y X = ⊤ := by
  have := centKer_normal hYX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (centKer Y X) with hb | ht
  · exfalso
    have hm := mem_centKer_of_le_centralizer heY h
    rw [hb, Subgroup.mem_bot] at hm
    exact he1 (congrArg Subtype.val hm)
  · exact ht

theorem normal_eq_top_of_prod {Y S₁ S₂ : Type*} [Group Y] [Group S₁] [Group S₂]
    [IsSimpleGroup S₁] [IsSimpleGroup S₂] (θ : Y ≃* S₁ × S₂) (K : Subgroup Y) [hK : K.Normal]
    {a : S₁} (ha : a ≠ 1) (haK : θ.symm (a, 1) ∈ K) {b : S₂} (hb : b ≠ 1)
    (hbK : θ.symm (1, b) ∈ K) : K = ⊤ := by
  have hKK : (K.map θ.toMonoidHom).Normal := hK.map θ.toMonoidHom θ.surjective
  have hmem : ∀ z : S₁ × S₂, θ.symm z ∈ K → z ∈ K.map θ.toMonoidHom := fun z hz =>
    ⟨θ.symm z, hz, by simp⟩
  have h1 : (K.map θ.toMonoidHom).comap (MonoidHom.inl S₁ S₂) = ⊤ := by
    have : ((K.map θ.toMonoidHom).comap (MonoidHom.inl S₁ S₂)).Normal := hKK.comap _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((K.map θ.toMonoidHom).comap (MonoidHom.inl S₁ S₂)) with h | h
    · exfalso
      have : a ∈ (K.map θ.toMonoidHom).comap (MonoidHom.inl S₁ S₂) := hmem (a, 1) haK
      rw [h, Subgroup.mem_bot] at this
      exact ha this
    · exact h
  have h2 : (K.map θ.toMonoidHom).comap (MonoidHom.inr S₁ S₂) = ⊤ := by
    have : ((K.map θ.toMonoidHom).comap (MonoidHom.inr S₁ S₂)).Normal := hKK.comap _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((K.map θ.toMonoidHom).comap (MonoidHom.inr S₁ S₂)) with h | h
    · exfalso
      have : b ∈ (K.map θ.toMonoidHom).comap (MonoidHom.inr S₁ S₂) := hmem (1, b) hbK
      rw [h, Subgroup.mem_bot] at this
      exact hb this
    · exact h
  rw [eq_top_iff]
  intro y _
  have hy : θ y ∈ K.map θ.toMonoidHom := by
    have e1 : ((θ y).1, (1 : S₂)) ∈ K.map θ.toMonoidHom := by
      have : (θ y).1 ∈ (K.map θ.toMonoidHom).comap (MonoidHom.inl S₁ S₂) := by
        rw [h1]; trivial
      exact this
    have e2 : ((1 : S₁), (θ y).2) ∈ K.map θ.toMonoidHom := by
      have : (θ y).2 ∈ (K.map θ.toMonoidHom).comap (MonoidHom.inr S₁ S₂) := by
        rw [h2]; trivial
      exact this
    have := Subgroup.mul_mem _ e1 e2
    simpa using this
  obtain ⟨k, hkK, hk⟩ := hy
  have : k = y := θ.injective hk
  rwa [this] at hkK

end CFSG.CGT.PushingUpLit.CGT6
