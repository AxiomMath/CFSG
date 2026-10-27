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
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LargeExtraspecial.DW

open Matrix Subgroup
open scoped MatrixGroups

@[expose] def cornerTransvection {N : ℕ} (hN : 2 ≤ N) : SL(N, ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection (i := ⟨0, by omega⟩) (j := ⟨N - 1, by omega⟩)
    (fun h => by simp only [Fin.mk.injEq] at h; omega) 1

theorem coe_cornerTransvection {N : ℕ} (hN : 2 ≤ N) :
    (cornerTransvection hN : Matrix (Fin N) (Fin N) (ZMod 2)) =
      1 + single ⟨0, by omega⟩ ⟨N - 1, by omega⟩ 1 :=
  rfl

@[expose] def DempwolffLn2Input : Prop :=
  ∀ (N : ℕ) (hN : 6 ≤ N) (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G),
    orderOf z = 2 →
    Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({cornerTransvection (N := N) (by omega)} :
        Set (SL(N, ZMod 2)))) →
    Nonempty (G ≃* SL(N, ZMod 2))

theorem center_specialLinearGroup_zmod_two_eq_bot (N : ℕ) :
    center (SL(N, ZMod 2)) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact (Subsingleton.elim A 1).symm ▸ one_mem _
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have h1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) r with rfl | rfl
    · rw [zero_pow hN.ne'] at hr
      exact absurd hr (by decide)
    · rfl
  rw [mem_bot]
  ext i j
  rw [← hrA, h1]
  simp

@[expose] noncomputable def slEquivPSL (N : ℕ) :
    SL(N, ZMod 2) ≃* PSL(N, ZMod 2) :=
  (QuotientGroup.quotientBot (G := SL(N, ZMod 2))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_specialLinearGroup_zmod_two_eq_bot N).symm)

theorem slEquivPSL_apply (N : ℕ) (A : SL(N, ZMod 2)) :
    slEquivPSL N A = (A : PSL(N, ZMod 2)) :=
  rfl

theorem nonempty_mulEquiv_psl {G : Type*} [Group G] {N : ℕ}
    (h : Nonempty (G ≃* SL(N, ZMod 2))) :
    Nonempty (G ≃* PSL(N, ZMod 2)) :=
  h.map fun e => e.trans (slEquivPSL N)

theorem DempwolffLn2Input.nonempty_mulEquiv_psl (hD : DempwolffLn2Input) {w : ℕ} (hw : 4 ≤ w)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G) (hz : orderOf z = 2)
    (hC : Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({cornerTransvection (N := w + 2) (by omega)} :
        Set (SL(w + 2, ZMod 2))))) :
    Nonempty (G ≃* PSL(w + 2, ZMod 2)) :=
  DW.nonempty_mulEquiv_psl (hD (w + 2) (by omega) G z hz hC)

end CFSG.LargeExtraspecial.DW
