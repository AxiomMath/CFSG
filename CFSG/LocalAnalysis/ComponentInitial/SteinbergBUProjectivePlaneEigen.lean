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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Polynomial

variable {K : Type*} [Field K] [Finite K] {p : ℕ}

theorem lt_card_of_isPrimitiveRoot [Fintype K] [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    p < Fintype.card K := by
  classical
  have h1 := Subgroup.card_le_card_group (rootsOfUnity p K)
  rw [hζ.card_rootsOfUnity, Nat.card_eq_fintype_card, Fintype.card_units] at h1
  have := Fintype.one_lt_card (α := K)
  omega

theorem charpoly_eq_X_pow_sub_one (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {A B : Matrix (Fin p) (Fin p) K} (hB : IsUnit B)
    (hAB : A * B = ζ • (B * A)) (hdet : A.det = 1) : A.charpoly = X ^ p - 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  obtain ⟨u, rfl⟩ := hB
  have hconj : (ζ • A).charpoly = A.charpoly := by
    have h := charpoly_units_conj' u A
    have hBA : ((u : Matrix (Fin p) (Fin p) K))⁻¹ * A * u = ζ • A := by
      rw [Matrix.mul_assoc, hAB, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.coe_units_inv,
        Units.inv_mul, Matrix.one_mul]
    rwa [hBA] at h
  have hdeg : A.charpoly.natDegree = p := by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hsc : ∀ t : K, scalar (Fin p) t - ζ • A = ζ • (scalar (Fin p) (ζ⁻¹ * t) - A) := by
    intro t
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [scalar_apply, mul_sub, mul_inv_cancel_left₀ hζ0]
    · simp [scalar_apply, hij]
  have heval : ∀ t : K, (A.charpoly.comp (C ζ⁻¹ * X)).eval t = A.charpoly.eval t := by
    intro t
    rw [eval_comp, eval_mul, eval_C, eval_X]
    conv_rhs => rw [← hconj]
    rw [eval_charpoly, eval_charpoly, hsc t, det_smul, Fintype.card_fin, hζ.pow_eq_one, one_mul]
  have hzero : A.charpoly.comp (C ζ⁻¹ * X) - A.charpoly = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := id) Function.injective_id
      (fun t => by rw [id, eval_sub, heval, sub_self]) ?_
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt natDegree_comp_le ?_
      rw [hdeg]
      rw [natDegree_C_mul_X _ (inv_ne_zero hζ0), mul_one]
      exact lt_card_of_isPrimitiveRoot hζ
    · rw [hdeg]
      exact lt_card_of_isPrimitiveRoot hζ
  have hcoeff : ∀ n, A.charpoly.coeff n * ζ⁻¹ ^ n = A.charpoly.coeff n := fun n => by
    have h := congrArg (fun P => P.coeff n) (sub_eq_zero.1 hzero)
    simp only [comp_C_mul_X_coeff] at h
    exact h
  have hmid : ∀ n, 0 < n → n < p → A.charpoly.coeff n = 0 := by
    intro n hn hnp
    have h := hcoeff n
    have hne : ζ⁻¹ ^ n ≠ 1 := hζ.inv.pow_ne_one_of_pos_of_lt hn.ne' hnp
    have h' : A.charpoly.coeff n * (ζ⁻¹ ^ n - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
    exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 hne)
  have hlead : A.charpoly.coeff p = 1 := by
    have h := (charpoly_monic A).coeff_natDegree
    rwa [hdeg] at h
  have hconst : A.charpoly.coeff 0 = -1 := by
    rw [coeff_zero_eq_eval_zero, eval_charpoly, map_zero, zero_sub, det_neg, hdet, mul_one,
      Fintype.card_fin, (hp.odd_of_ne_two hp2).neg_one_pow]
  ext n
  rw [coeff_sub, coeff_X_pow, coeff_one]
  rcases Nat.lt_trichotomy n p with hn | hn | hn
  · rcases Nat.eq_zero_or_pos n with h0 | hn0
    · rw [h0, hconst, ite_eq_right_iff.2 fun h => absurd h hp.ne_zero.symm,
        ite_eq_left_iff.2 fun h => absurd rfl h]
      ring
    · rw [hmid n hn0 hn, ite_eq_right_iff.2 fun h => absurd h hn.ne,
        ite_eq_right_iff.2 fun h => absurd h hn0.ne']
      ring
  · rw [hn, hlead, ite_eq_left_iff.2 fun h => absurd rfl h,
      ite_eq_right_iff.2 fun h => absurd h hp.ne_zero]
    ring
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hn),
      ite_eq_right_iff.2 fun h => absurd h hn.ne', ite_eq_right_iff.2 fun h => by omega]
    ring

theorem exists_eigenbasis (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A B : Matrix (Fin p) (Fin p) K} (hB : IsUnit B) (hAB : A * B = ζ • (B * A))
    (hdet : A.det = 1) :
    ∃ P : GL (Fin p) K, A = (P : Matrix (Fin p) (Fin p) K) *
      diagonal (fun i : Fin p => ζ ^ (i : ℕ)) *
        ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
  classical
  have hcp := charpoly_eq_X_pow_sub_one hp hp2 hζ hB hAB hdet
  have hev : ∀ i : Fin p, ∃ v : Fin p → K, v ≠ 0 ∧ A *ᵥ v = ζ ^ (i : ℕ) • v := by
    intro i
    have h0 : (scalar (Fin p) (ζ ^ (i : ℕ)) - A).det = 0 := by
      rw [← eval_charpoly, hcp, eval_sub, eval_pow, eval_X, eval_one, ← pow_mul, mul_comm,
        pow_mul, hζ.pow_eq_one, one_pow, sub_self]
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 h0
    refine ⟨v, hv0, ?_⟩
    rw [sub_mulVec, sub_eq_zero] at hv
    rw [← hv, scalar_apply]
    funext j
    rw [mulVec_diagonal]
    rfl
  choose v hv0 hv using hev
  have hli : LinearIndependent K v := by
    refine Module.End.eigenvectors_linearIndependent' (mulVecLin A) (fun i : Fin p => ζ ^ (i : ℕ))
      ?_ v fun i => ?_
    · intro i j hij
      exact Fin.ext (hζ.pow_inj i.2 j.2 hij)
    · rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
      exact ⟨hv i, hv0 i⟩
  set Pm : Matrix (Fin p) (Fin p) K := Matrix.of fun r c => v c r
  have hPcol : Pm.col = v := by
    funext c r
    rfl
  have hPu : IsUnit Pm := Matrix.linearIndependent_cols_iff_isUnit.1 (by rw [hPcol]; exact hli)
  refine ⟨hPu.unit, ?_⟩
  have hAP : A * Pm = Pm * diagonal (fun i : Fin p => ζ ^ (i : ℕ)) := by
    ext r c
    rw [mul_diagonal]
    have h := congrFun (hv c) r
    rw [Pi.smul_apply, smul_eq_mul] at h
    change (A * Pm) r c = v c r * ζ ^ (c : ℕ)
    rw [mul_comm, ← h]
    rfl
  rw [IsUnit.unit_spec, ← hAP, Matrix.mul_assoc]
  change A = A * (((hPu.unit : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
    ((hPu.unit⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
