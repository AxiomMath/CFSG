module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem dvd_card_sub_card_inf_centralizer {p : ℕ} [Fact p.Prime] {R : Subgroup G} {g : G}
    (hg : orderOf g = p) (hgN : g ∈ normalizer (R : Set G)) :
    p ∣ Nat.card R - Nat.card (R ⊓ centralizer ({g} : Set G) : Subgroup G) := by
  classical
  set K : Subgroup G := zpowers g with hK
  have hKN : K ≤ normalizer (R : Set G) := zpowers_le.mpr hgN
  let φ : ↥K →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hKN)
  letI : MulAction ↥K ↥R := MulAction.compHom ↥R φ
  have hKp : IsPGroup p ↥K := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hK, Nat.card_zpowers, hg, pow_one]
  have hmod := hKp.card_modEq_card_fixedPoints ↥R
  have hsmul : ∀ (k : ↥K) (r : ↥R), ((k • r : ↥R) : G) = (k : G) * r * (k : G)⁻¹ := by
    intro k r
    exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hfix : ∀ r : ↥R, r ∈ MulAction.fixedPoints ↥K ↥R ↔ g * (r : G) = (r : G) * g := by
    intro r
    constructor
    · intro h
      have h1 := h ⟨g, mem_zpowers g⟩
      have h2 := congrArg Subtype.val h1
      rw [hsmul] at h2
      simp only at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2)
    · intro h k
      apply Subtype.ext
      rw [hsmul]
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp k.2
      have hc : Commute g (r : G) := h
      have : (k : G) * r = r * k := by
        rw [← hn]
        exact ((hc.zpow_left n).eq)
      rw [this, mul_inv_cancel_right]
  have hcard : Nat.card (MulAction.fixedPoints ↥K ↥R) =
      Nat.card (R ⊓ centralizer ({g} : Set G) : Subgroup G) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun r => ⟨(r.1 : G), r.1.2, ?_⟩
        invFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.mp s.2).1⟩, ?_⟩
        left_inv := fun r => rfl
        right_inv := fun s => rfl }
    · exact mem_centralizer_singleton_iff.mpr ((hfix r.1).mp r.2).symm
    · rw [hfix]
      exact (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp s.2).2).symm
  rw [hcard] at hmod
  have hle : Nat.card (R ⊓ centralizer ({g} : Set G) : Subgroup G) ≤ Nat.card R :=
    Subgroup.card_le_of_le inf_le_left
  exact (Nat.modEq_iff_dvd' hle).mp hmod.symm

theorem eq_seven_of_not_centralizes {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {R : Subgroup G} {g : G}
    (hg : orderOf g = p) (hgN : g ∈ normalizer (R : Set G)) (hR : Nat.card R ∣ 8)
    (hnc : ∃ y ∈ R, g * y ≠ y * g) : p = 7 ∧ Nat.card R = 8 := by
  have hd := dvd_card_sub_card_inf_centralizer hg hgN
  set C : Subgroup G := R ⊓ centralizer ({g} : Set G) with hC
  have hCR : Nat.card C ∣ Nat.card R := Subgroup.card_dvd_of_le inf_le_left
  have hCne : Nat.card C ≠ Nat.card R := by
    intro h
    obtain ⟨y, hy, hgy⟩ := hnc
    have hCeq : C = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hyC : y ∈ C := hCeq ▸ hy
    exact hgy (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyC).2).symm
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hlt : Nat.card C < Nat.card R := lt_of_le_of_ne (Nat.le_of_dvd hRpos hCR) hCne
  have h8R : Nat.card R ∈ ({1, 2, 4, 8} : Finset ℕ) := by
    have : Nat.card R ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hR, by norm_num⟩
    simpa [show Nat.divisors 8 = {1, 2, 4, 8} by decide] using this
  have h8C : Nat.card C ∣ 8 := hCR.trans hR
  have h8C' : Nat.card C ∈ ({1, 2, 4, 8} : Finset ℕ) := by
    have : Nat.card C ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨h8C, by norm_num⟩
    simpa [show Nat.divisors 8 = {1, 2, 4, 8} by decide] using this
  have hpos : 0 < Nat.card R - Nat.card C := by omega
  have hple : p ≤ Nat.card R - Nat.card C := Nat.le_of_dvd hpos hd
  have hRC : Nat.card R = 8 ∧ Nat.card C = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at h8R h8C'
    rcases h8R with h | h | h | h <;> rcases h8C' with h' | h' | h' | h'
    all_goals first
      | exact ⟨h, h'⟩
      | (rw [h, h'] at hple hlt hd
         first
           | omega
           | (exfalso
              have h6 : p ∣ 2 * 3 := by simpa using hd
              rcases (Fact.out : p.Prime).dvd_mul.mp h6 with h2 | h3
              · have := Nat.le_of_dvd (by norm_num) h2; omega
              · have := Nat.le_of_dvd (by norm_num) h3; omega))
  rw [hRC.1, hRC.2] at hd
  have hp7 : p ∣ 7 := by simpa using hd
  exact ⟨(Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num : Nat.Prime 7)).mp hp7,
    hRC.1⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
