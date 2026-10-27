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

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_isPGroup_zpowers {p r N : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hrp : r ≠ p) {W : Subgroup G} (hW : Nat.card W = p ^ N)
    (hZ : ∀ j : ℕ, 0 < j → j ≤ N → ¬ r ∣ p ^ j - 1) {m : G}
    (hm : m ∈ normalizer (W : Set G)) (hmr : IsPGroup r (zpowers m)) :
    ∀ w ∈ W, m * w = w * m := by
  classical
  have hAN : zpowers m ≤ normalizer (W : Set G) := (zpowers_le).mpr hm
  let ρ : zpowers m →* Equiv.Perm W :=
    (MulAut.toPerm W).comp ((W.normalizerMonoidHom).comp (inclusion hAN))
  let _inst : MulAction (zpowers m) W := MulAction.compHom W ρ
  have hmod := hmr.card_modEq_card_fixedPoints W
  set C : Subgroup W := (centralizer ({m} : Set G)).subgroupOf W with hC
  have hfix : MulAction.fixedPoints (zpowers m) W = (C : Set W) := by
    ext w
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, hC, mem_subgroupOf,
      mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := h ⟨m, mem_zpowers m⟩
      have h2 := congrArg (Subtype.val : W → G) h1
      change m * (w : G) * m⁻¹ = (w : G) at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · intro h a
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp a.2
      apply Subtype.ext
      change (a : G) * (w : G) * (a : G)⁻¹ = (w : G)
      rw [← hk, mul_inv_eq_iff_eq_mul]
      exact (Commute.zpow_left (show Commute m (w : G) from h.symm) k).eq
  have hcard : Nat.card (MulAction.fixedPoints (zpowers m) W) = Nat.card C := by
    rw [hfix]
    rfl
  rw [hcard] at hmod
  obtain ⟨d, hd, hCd⟩ := (Nat.dvd_prime_pow hp.out).mp (hW ▸ Subgroup.card_subgroup_dvd_card C)
  have hCW : C = ⊤ := by
    by_contra hne
    have hlt : Nat.card C < Nat.card W := by
      refine lt_of_le_of_ne (Nat.card_le_card_of_injective _ (Subtype.val_injective)) ?_
      intro heq
      exact hne (Subgroup.eq_top_of_card_eq C heq)
    rw [hW, hCd] at hlt
    rw [hW, hCd] at hmod
    have hdN : d < N := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp hlt
    have hdvd : r ∣ p ^ N - p ^ d := by
      have := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hp.out.pos hdN.le)).mp hmod.symm
      exact this
    have hfac : p ^ N - p ^ d = p ^ d * (p ^ (N - d) - 1) := by
      have h1 : p ^ N = p ^ d * p ^ (N - d) := by rw [← pow_add]; congr 1; omega
      rw [h1, Nat.mul_sub, mul_one]
    rw [hfac] at hdvd
    rcases hr.out.dvd_mul.mp hdvd with h | h
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hr.out hp.out).mp (hr.out.dvd_of_dvd_pow h))
    · exact hZ (N - d) (by omega) (by omega) h
  intro w hw
  have : (⟨w, hw⟩ : W) ∈ C := by rw [hCW]; trivial
  have h2 := mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp this)
  exact h2.symm

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
