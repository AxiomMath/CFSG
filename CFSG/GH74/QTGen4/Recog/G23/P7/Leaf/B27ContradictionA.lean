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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.B27A

open Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) (ZMod 3)

theorem sl23_inv_aux : ∀ A : Mat2, A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 → A * A = 1 →
    A = 1 ∨ A = -1 := by
  decide +kernel

theorem sl23_cent_aux : ∀ A : Mat2, A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 →
    (∀ B : Mat2, B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 → A * B = B * A) → A = 1 ∨ A = -1 := by
  decide +kernel

theorem sl23_card_aux :
    (Finset.univ.filter (fun A : Mat2 => A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1)).card = 24 := by
  decide +kernel

theorem sl23_det (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    (A : Mat2) 0 0 * (A : Mat2) 1 1 - (A : Mat2) 0 1 * (A : Mat2) 1 0 = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe A
  rwa [Matrix.det_fin_two] at this

theorem sl23_card : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  let e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) ≃
      {A : Mat2 // A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1} :=
    { toFun := fun A => ⟨A, sl23_det A⟩
      invFun := fun A => ⟨A.1, by rw [Matrix.det_fin_two]; exact A.2⟩
      left_inv := fun A => rfl
      right_inv := fun A => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, ← sl23_card_aux]

theorem sl23_exists_noncomm :
    ∃ A B : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), A * B ≠ B * A := by
  let A₀ : Mat2 := Matrix.of ![![1, 1], ![0, 1]]
  let B₀ : Mat2 := Matrix.of ![![1, 0], ![1, 1]]
  have hA : A₀ 0 0 * A₀ 1 1 - A₀ 0 1 * A₀ 1 0 = 1 := by decide
  have hB : B₀ 0 0 * B₀ 1 1 - B₀ 0 1 * B₀ 1 0 = 1 := by decide
  have hAB : A₀ * B₀ ≠ B₀ * A₀ := by decide
  refine ⟨⟨A₀, by rw [Matrix.det_fin_two]; exact hA⟩, ⟨B₀, by rw [Matrix.det_fin_two]; exact hB⟩,
    fun heq => hAB (congrArg Subtype.val heq)⟩

theorem sl23_involution (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (h : A * A = 1) :
    (A : Mat2) = 1 ∨ (A : Mat2) = -1 := by
  have h2 : (A : Mat2) * (A : Mat2) = 1 := by
    have := congrArg Subtype.val h
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  exact sl23_inv_aux _ (sl23_det A) h2

theorem sl23_central (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (h : ∀ B : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), A * B = B * A) :
    (A : Mat2) = 1 ∨ (A : Mat2) = -1 := by
  have h2 : ∀ B : Mat2, B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 → (A : Mat2) * B = B * (A : Mat2) := by
    intro B hB
    have hdet : B.det = 1 := by rw [Matrix.det_fin_two]; exact hB
    have := congrArg Subtype.val (h ⟨B, hdet⟩)
    exact this
  exact sl23_cent_aux _ (sl23_det A) h2

theorem card_ker_mul_card_range {V : Type*} [AddCommGroup V] [Finite V] (f : V →+ V) :
    Nat.card f.ker * Nat.card f.range = Nat.card V := by
  have h := AddSubgroup.card_mul_index f.ker
  rwa [AddSubgroup.index_ker] at h

theorem card_ker_ge_nine {V : Type*} [AddCommGroup V] [Finite V] (T : V →+ V)
    (hT : ∀ x, T (T (T x)) = 0) (hV : Nat.card V = 81) :
    9 ≤ Nat.card T.ker := by
  have h1 : Nat.card T.ker * Nat.card T.range = 81 := by
    rw [card_ker_mul_card_range, hV]
  let TI : T.range →+ T.range :=
    AddMonoidHom.codRestrict (T.comp T.range.subtype) T.range (fun c => ⟨c.1, rfl⟩)
  have hTI : ∀ c : T.range, ((TI c : T.range) : V) = T c.1 := fun c => rfl
  have h2 : Nat.card T.range = Nat.card TI.ker * Nat.card TI.range :=
    (card_ker_mul_card_range TI).symm
  have hk : Nat.card TI.ker ≤ Nat.card T.ker := by
    refine Nat.card_le_card_of_injective
      (fun x : TI.ker => (⟨x.1.1, ?_⟩ : T.ker)) ?_
    · have hx : TI x.1 = 0 := x.2
      have := congrArg (fun y : T.range => (y : V)) hx
      simpa [hTI] using this
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg (fun w : T.ker => (w : V)) hxy
  have hr : Nat.card TI.range ≤ Nat.card T.ker := by
    refine Nat.card_le_card_of_injective
      (fun y : TI.range => (⟨y.1.1, ?_⟩ : T.ker)) ?_
    · obtain ⟨x, hx⟩ := y.2
      obtain ⟨v, hv⟩ := x.2
      have hy : (y.1 : V) = T (x : V) := by
        rw [← hx]; rfl
      rw [AddMonoidHom.mem_ker, hy, ← hv, hT]
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg (fun w : T.ker => (w : V)) hxy
  have hbound : 81 ≤ Nat.card T.ker ^ 3 := by
    have h4 : Nat.card T.ker * Nat.card T.range ≤ Nat.card T.ker ^ 3 := by
      rw [h2, pow_three]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hk hr)
    rw [← h1]
    exact h4
  have hd : Nat.card T.ker ∣ 81 := ⟨Nat.card T.range, h1.symm⟩
  by_contra hlt
  push Not at hlt
  have hpos : 0 < Nat.card T.ker := by
    rcases Nat.eq_zero_or_pos (Nat.card T.ker) with h0 | h0
    · rw [h0] at hd; norm_num at hd
    · exact h0
  interval_cases hk' : Nat.card T.ker <;> revert hd hbound <;> norm_num

theorem isKleinFour_of_sq {E : Type*} [Group E] [Finite E] (hcard : Nat.card E = 4)
    (hsq : ∀ x : E, x * x = 1) : IsKleinFour E := by
  have hnt : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  refine ⟨hcard, ?_⟩
  have h1 : Monoid.exponent E ∣ 2 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    rw [pow_two]
    exact hsq g
  have h2 : Monoid.exponent E ≠ 1 := by
    rw [Ne, Monoid.exp_eq_one_iff]
    exact not_subsingleton E
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact absurd h h2
  · exact h

theorem card_GL3_F3 : Nat.card (GL (Fin 3) (ZMod 3)) = 11232 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_three, ZMod.card]

noncomputable def basis_of_indep3 {A : Type*} [AddCommGroup A] [Module (ZMod 3) A] [Finite A]
    (hA : Nat.card A = 27) (v : Fin 3 → A) (hv : LinearIndependent (ZMod 3) v) :
    Module.Basis (Fin 3) (ZMod 3) A := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  have h2 : Fintype.card A = 27 := by rw [← hA, Nat.card_eq_fintype_card]
  have h1 : Fintype.card A = Fintype.card (ZMod 3) ^ Module.finrank (ZMod 3) A :=
    Module.card_eq_pow_finrank
  rw [ZMod.card, h2] at h1
  have hfr : Module.finrank (ZMod 3) A = 3 := by
    have h3 : (3 : ℕ) ^ (Module.finrank (ZMod 3) A) = 3 ^ 3 := by rw [← h1]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  have hfin : Fintype.card (Fin 3) = Module.finrank (ZMod 3) A := by
    rw [hfr]; simp
  exact basisOfLinearIndependentOfCardEqFinrank hv hfin

theorem basis_of_indep3_apply {A : Type*} [AddCommGroup A] [Module (ZMod 3) A] [Finite A]
    (hA : Nat.card A = 27) (v : Fin 3 → A) (hv : LinearIndependent (ZMod 3) v) (i : Fin 3) :
    basis_of_indep3 hA v hv i = v i := by
  unfold basis_of_indep3
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

end CFSG.GH74.QTGen4.Recog.G23.P7.B27A

end
