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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

theorem finite_fields_common_extension (p : ℕ) [Fact p.Prime] {F D : Type*} [Field F] [Field D]
    [Finite F] [Finite D] [CharP F p] [CharP D p] {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hF : Nat.card F = p ^ n) (hD : Nat.card D = p ^ d) :
    ∃ (e : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E p) (ιF : F →+* E)
      (ιD : D →+* E), 1 ≤ e ∧ n ∣ e ∧ d ∣ e ∧ Nat.card E = p ^ e ∧
      Function.Injective ιF ∧ Function.Injective ιD ∧
      (∀ x : ℕ, ιF (x : F) = ιD (x : D)) ∧
      (∀ a : D, (ιD a) ^ (p ^ d) = ιD a) ∧
      (∀ (b : F) (j : ℕ), (ιF b) ^ (p ^ j) = ιF (b ^ (p ^ j))) := by
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  let _ : Algebra (ZMod p) D := ZMod.algebra D p
  have : Fintype F := Fintype.ofFinite F
  have : Fintype D := Fintype.ofFinite D
  have hfF : Module.finrank (ZMod p) F = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
    rw [ZMod.card, Fintype.card_eq_nat_card, hF] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  have hfD : Module.finrank (ZMod p) D = d := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := D)
    rw [ZMod.card, Fintype.card_eq_nat_card, hD] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  have hnd : n * d ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hE : Module.finrank (ZMod p) (GaloisField p (n * d)) = n * d :=
    GaloisField.finrank p hnd
  obtain ⟨ιF⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := F)
    (L := GaloisField p (n * d)) (by rw [hfF, hE]; exact dvd_mul_right n d)
  obtain ⟨ιD⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := D)
    (L := GaloisField p (n * d)) (by rw [hfD, hE]; exact dvd_mul_left d n)
  refine ⟨n * d, GaloisField p (n * d), inferInstance, inferInstance, inferInstance,
    ιF.toRingHom, ιD.toRingHom, Nat.one_le_iff_ne_zero.mpr hnd, dvd_mul_right n d,
    dvd_mul_left d n, ?_,
    ιF.toRingHom.injective, ιD.toRingHom.injective, ?_, ?_, ?_⟩
  · exact GaloisField.card p (n * d) hnd
  · intro x
    simp
  · intro a
    have h1 : (ιD.toRingHom a) ^ (p ^ d) = ιD.toRingHom (a ^ (p ^ d)) := (map_pow _ _ _).symm
    rw [h1]
    congr 1
    have := FiniteField.pow_card a
    rwa [Fintype.card_eq_nat_card, hD] at this
  · intro b j
    exact (map_pow ιF.toRingHom b (p ^ j)).symm

end CFSG.QuasithinUnique.Setup.SL2Modules
