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

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

variable {G : Type*} [Group G] [Finite G] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [DistribMulAction G M]

theorem exists_coboundary_of_odd_index (S : Subgroup G) (hS : ¬ 2 ∣ S.index) (c : G → M)
    (hc : ∀ g h, c (g * h) = c g + g • c h) (hS0 : ∀ s ∈ S, c s = 0) :
    ∃ m : M, ∀ g, c g = g • m - m := by
  classical
  have : Fintype (G ⧸ S) := Fintype.ofFinite _
  have hcs : ∀ g (s : G), s ∈ S → c (g * s) = c g := fun g s hs => by
    rw [hc, hS0 s hs, smul_zero, add_zero]
  let f : G ⧸ S → M := Quotient.lift c (fun a b hab => by
    have hab' : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.mp hab
    have h2 := hcs a (a⁻¹ * b) hab'
    simpa using h2.symm)
  have hf : ∀ x : G, f (x : G ⧸ S) = c x := fun x => rfl
  set s : M := ∑ q : G ⧸ S, f q with hs
  have hN : ((Fintype.card (G ⧸ S) : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_one_iff_odd]
    have : Fintype.card (G ⧸ S) = S.index := by
      rw [Subgroup.index, Nat.card_eq_fintype_card]
    rw [this]
    exact Nat.odd_iff.mpr (by omega)
  refine ⟨-s, fun g => ?_⟩
  have key : s = ∑ q : G ⧸ S, f (g • q) :=
    (Equiv.sum_comp (MulAction.toPerm g) f).symm
  have hstep : ∀ q : G ⧸ S, f (g • q) = c g + g • f q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have : g • (x : G ⧸ S) = ((g * x : G) : G ⧸ S) := rfl
      rw [this, hf, hf, hc]
  have h2 : ∑ q : G ⧸ S, f (g • q) = Fintype.card (G ⧸ S) • c g + g • s := by
    rw [Finset.sum_congr rfl (fun q _ => hstep q), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, hs, Finset.smul_sum]
  have h3 : Fintype.card (G ⧸ S) • c g = c g := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hN, one_smul]
  rw [← key, h3] at h2
  rw [smul_neg]
  have h4 : c g = s - g • s := by
    rw [eq_sub_iff_add_eq]
    exact h2.symm
  rw [h4]
  abel

omit [Finite G] [Module (ZMod 2) M] in
theorem fixed_of_coboundary_of_vanishes (S : Subgroup G) (c : G → M) (m : M)
    (hcm : ∀ g, c g = g • m - m) (hS0 : ∀ s ∈ S, c s = 0) : ∀ s ∈ S, s • m = m := by
  intro s hs
  have := hS0 s hs
  rw [hcm] at this
  exact sub_eq_zero.mp this

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
