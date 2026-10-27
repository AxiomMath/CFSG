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
public import Mathlib.Tactic.Basify
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

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33

theorem false_of_small_centralizers {M : Type} [Group M] [Finite M] (Qm : Subgroup M)
    (hQ9 : Nat.card Qm = 9) (hQc : ∀ x ∈ Qm, ∀ y ∈ Qm, x * y = y * x)
    (hQ3 : ∀ x ∈ Qm, x ^ 3 = 1) (hM : Nat.card M = 6048)
    (hC : ∀ x ∈ Qm, x ≠ 1 → Nat.card (Subgroup.centralizer ({x} : Set M)) ≤ 9) : False := by
  have hQp : IsPGroup 3 Qm := IsPGroup.of_card (n := 2) (by rw [hQ9]; norm_num)
  obtain ⟨S, hQS⟩ := hQp.exists_le_sylow
  have hSp : IsPGroup 3 (S : Subgroup M) := S.isPGroup'
  have hS27 : Nat.card (S : Subgroup M) = 27 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hSp
    have hidx := S.not_dvd_index
    have h := Subgroup.card_mul_index (S : Subgroup M)
    rw [hn, hM] at h
    have hn6 : n ≤ 8 := by
      by_contra hc
      have h9 : 3 ^ 9 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hi : 0 < (S : Subgroup M).index := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hidx)
      have : 3 ^ n ≤ 3 ^ n * (S : Subgroup M).index := Nat.le_mul_of_pos_right _ hi
      omega
    rw [hn]
    interval_cases n <;> first | omega | (exfalso; apply hidx; omega)
  haveI : Nontrivial (S : Subgroup M) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hS27]; norm_num)
  haveI := hSp.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : Subgroup.center (S : Subgroup M))
  have hzS : (z : M) ∈ (S : Subgroup M) := z.2
  have hzne : (z : M) ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hzcomm : ∀ s ∈ (S : Subgroup M), s * (z : M) = (z : M) * s := fun s hs => by
    have := Subgroup.mem_center_iff.mp hzc ⟨s, hs⟩
    exact congrArg Subtype.val this
  by_cases hzQ : (z : M) ∈ Qm
  ·
    have hle : (S : Subgroup M) ≤ Subgroup.centralizer ({(z : M)} : Set M) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzcomm s hs
    have := Subgroup.card_le_of_le hle
    have := hC (z : M) hzQ hzne
    omega
  ·
    obtain ⟨x, hxQ, hx1⟩ : ∃ x ∈ Qm, x ≠ 1 := by
      by_contra h
      push Not at h
      have : Qm = ⊥ := (Subgroup.eq_bot_iff_forall Qm).mpr h
      rw [this, Subgroup.card_bot] at hQ9
      omega
    have hle : Qm ⊔ Subgroup.zpowers (z : M) ≤ Subgroup.centralizer ({x} : Set M) := by
      refine sup_le ?_ ?_
      · intro q hq
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hQc q hq x hxQ
      · rw [Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hzcomm x (hQS hxQ)).symm
    have hlt : Qm < Qm ⊔ Subgroup.zpowers (z : M) := by
      refine lt_of_le_of_ne le_sup_left fun h => hzQ ?_
      have : Subgroup.zpowers (z : M) ≤ Qm := by
        calc Subgroup.zpowers (z : M) ≤ Qm ⊔ Subgroup.zpowers (z : M) := le_sup_right
          _ = Qm := h.symm
      exact this (Subgroup.mem_zpowers _)
    have h1 : 9 < Nat.card (Qm ⊔ Subgroup.zpowers (z : M) : Subgroup M) := by
      rw [← hQ9]
      exact Subgroup.card_lt_of_lt hlt
    have := Subgroup.card_le_of_le hle
    have := hC x hxQ hx1
    omega

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33
