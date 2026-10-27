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

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

theorem centralizer_le_normalizer_of_normal {G : Type*} [Group G] {L J : Subgroup G} {x : G}
    (hn : ∀ c ∈ centralizer ({x} : Set G), J.map (MulAut.conj c).toMonoidHom = J)
    (hz : ∃ z ∈ J, z ≠ 1 ∧ z * z = 1)
    (hG5 : ∀ z ∈ J, z ≠ 1 → z * z = 1 →
      ∃ k ∈ L, k * x * k⁻¹ = x * z ∧ J ⊔ J.map (MulAut.conj k).toMonoidHom = L) :
    centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  have key : ∀ d ∈ centralizer ({x} : Set G),
      L.map (MulAut.conj d).toMonoidHom = L := by
    intro d hd
    have hdJ : J.map (MulAut.conj d).toMonoidHom = J := hn d hd
    have map_conj_mul : ∀ a b : G,
        J.map (MulAut.conj (a * b)).toMonoidHom =
          (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
      intro a b
      have h : (MulAut.conj (a * b)).toMonoidHom =
          (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
        ext g
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [h]
      exact (Subgroup.map_map (K := J) (g := (MulAut.conj a).toMonoidHom)
        (f := (MulAut.conj b).toMonoidHom)).symm
    obtain ⟨z₁, hz₁J, hz₁ne, hz₁sq⟩ := hz
    obtain ⟨k, hkL, hkx, hkLsup⟩ := hG5 z₁ hz₁J hz₁ne hz₁sq
    let z₁' : G := MulAut.conj d z₁
    have hz₁'J : z₁' ∈ J := by
      have hmem : MulAut.conj d z₁ ∈ J.map (MulAut.conj d).toMonoidHom :=
        ⟨z₁, hz₁J, rfl⟩
      rwa [hdJ] at hmem
    have hz₁'ne : z₁' ≠ 1 := by
      intro h
      exact hz₁ne ((MulAut.conj d).injective (h.trans (map_one (MulAut.conj d)).symm))
    have hz₁'sq : z₁' * z₁' = 1 := by
      rw [show z₁' = MulAut.conj d z₁ from rfl, ← map_mul, hz₁sq, map_one]
    obtain ⟨k', hk'L, hk'x, hk'Lsup⟩ := hG5 z₁' hz₁'J hz₁'ne hz₁'sq
    let m : G := k'⁻¹ * (d * k * d⁻¹)
    have hmx : m * x * m⁻¹ = x := by
      have hwx : (d * k * d⁻¹) * x * (d * k * d⁻¹)⁻¹ = x * z₁' := by
        have hdx : d * x * d⁻¹ = x := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp hd]
          group
        have hdx' : d⁻¹ * x * d = x := by
          rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hd]; group
        calc (d * k * d⁻¹) * x * (d * k * d⁻¹)⁻¹
            = d * k * (d⁻¹ * x * d) * k⁻¹ * d⁻¹ := by group
          _ = d * k * x * k⁻¹ * d⁻¹ := by rw [hdx']
          _ = d * (k * x * k⁻¹) * d⁻¹ := by group
          _ = d * (x * z₁) * d⁻¹ := by rw [hkx]
          _ = (d * x * d⁻¹) * (d * z₁ * d⁻¹) := by group
          _ = x * z₁' := by rw [hdx]; rfl
      calc m * x * m⁻¹
          = k'⁻¹ * ((d * k * d⁻¹) * x * (d * k * d⁻¹)⁻¹) * k' := by
            simp only [m]; group
        _ = k'⁻¹ * (x * z₁') * k' := by rw [hwx]
        _ = x := by rw [← hk'x]; group
    have hm : m ∈ centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc m * x = m * x * m⁻¹ * m := by group
        _ = x * m := by rw [hmx]
    have hmJ : J.map (MulAut.conj m).toMonoidHom = J := hn m hm
    have hdkm : d * k = k' * (m * d) := by
      simp only [m]
      group
    have hJmd : J.map (MulAut.conj (m * d)).toMonoidHom = J := by
      rw [map_conj_mul m d, hdJ, hmJ]
    have hJdkm : J.map (MulAut.conj (d * k)).toMonoidHom =
        J.map (MulAut.conj k').toMonoidHom := by
      rw [hdkm, map_conj_mul k' (m * d), hJmd]
    calc L.map (MulAut.conj d).toMonoidHom
        = (J ⊔ J.map (MulAut.conj k).toMonoidHom).map
            (MulAut.conj d).toMonoidHom := by rw [hkLsup]
      _ = J.map (MulAut.conj d).toMonoidHom ⊔
            (J.map (MulAut.conj k).toMonoidHom).map (MulAut.conj d).toMonoidHom := by
            rw [Subgroup.map_sup]
      _ = J ⊔ J.map (MulAut.conj k').toMonoidHom := by
            rw [hdJ, ← map_conj_mul d k, hJdkm]
      _ = L := hk'Lsup
  intro c hc
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact key c hc

end CFSG.EvenSporadicStandard.M12Std.PropA
