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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.Generic

open Module

theorem involution_isCompl {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {V : Type*} [AddCommGroup V]
    [Module F V] (f : V →ₗ[F] V) (hf : ∀ v, f (f v) = v) :
    IsCompl (LinearMap.ker (f + LinearMap.id)) (LinearMap.ker (f - LinearMap.id)) := by
  classical
  let gp : V →ₗ[F] V := f + LinearMap.id
  let gm : V →ₗ[F] V := f - LinearMap.id
  have hgp : ∀ v, gp v = f v + v := fun v => rfl
  have hgm : ∀ v, gm v = f v - v := fun v => rfl
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hvW hvU
    have h1 : f v + v = 0 := by rw [← hgp]; exact hvW
    have h2' : f v - v = 0 := by rw [← hgm]; exact hvU
    have h3 : (2 : F) • v = 0 := by
      have : (2 : F) • v = (f v + v) - (f v - v) := by
        rw [two_smul]; abel
      rw [this, h1, h2', sub_zero]
    exact (smul_eq_zero.1 h3).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have h1 : v - f v ∈ LinearMap.ker gp := by
      change gp (v - f v) = 0
      rw [hgp, map_sub, hf]; abel
    have h2' : v + f v ∈ LinearMap.ker gm := by
      change gm (v + f v) = 0
      rw [hgm, map_add, hf]; abel
    have : v = (2 : F)⁻¹ • (v - f v) + (2 : F)⁻¹ • (v + f v) := by
      rw [← smul_add, show v - f v + (v + f v) = (2 : F) • v by rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [this]
    exact Submodule.add_mem_sup ((LinearMap.ker gp).smul_mem _ h1)
      ((LinearMap.ker gm).smul_mem _ h2')

theorem involution_finrank_add {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (f : V →ₗ[F] V)
    (hf : ∀ v, f (f v) = v) :
    finrank F (LinearMap.ker (f + LinearMap.id)) + finrank F (LinearMap.ker (f - LinearMap.id)) =
      finrank F V :=
  Submodule.finrank_add_eq_of_isCompl (involution_isCompl h2 f hf)

theorem exists_basis_involution' {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (f : V →ₗ[F] V)
    (hf : ∀ v, f (f v) = v) (a b : ℕ)
    (ha : finrank F (LinearMap.ker (f + LinearMap.id)) = a)
    (hb : finrank F (LinearMap.ker (f - LinearMap.id)) = b) :
    ∃ B : Basis (Fin a ⊕ Fin b) F V,
      (∀ i, f (B (Sum.inl i)) = - B (Sum.inl i)) ∧ (∀ j, f (B (Sum.inr j)) = B (Sum.inr j)) := by
  classical
  let gp : V →ₗ[F] V := f + LinearMap.id
  let gm : V →ₗ[F] V := f - LinearMap.id
  have hgp : ∀ v, gp v = f v + v := fun v => rfl
  have hgm : ∀ v, gm v = f v - v := fun v => rfl
  have hcompl : IsCompl (LinearMap.ker gp) (LinearMap.ker gm) := involution_isCompl h2 f hf
  let bW := Module.finBasisOfFinrankEq F (LinearMap.ker gp) ha
  let bU := Module.finBasisOfFinrankEq F (LinearMap.ker gm) hb
  refine ⟨(bW.prod bU).map (Submodule.prodEquivOfIsCompl _ _ hcompl), fun i => ?_, fun j => ?_⟩
  · have : (((bW.prod bU).map (Submodule.prodEquivOfIsCompl _ _ hcompl)) (Sum.inl i)) =
        (bW i : V) := by
      rw [Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
      simp
    rw [this]
    have h1 : gp (bW i : V) = 0 := (bW i).2
    rw [hgp] at h1
    exact eq_neg_of_add_eq_zero_left h1
  · have : (((bW.prod bU).map (Submodule.prodEquivOfIsCompl _ _ hcompl)) (Sum.inr j)) =
        (bU j : V) := by
      rw [Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
      simp
    rw [this]
    have h1 : gm (bU j : V) = 0 := (bU j).2
    rw [hgm] at h1
    exact sub_eq_zero.1 h1

theorem exists_conj_diag4 {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (t : Matrix (Fin 4) (Fin 4) F)
    (ht : t * t = 1)
    (hdim : finrank F (LinearMap.ker (Matrix.toLin' t + LinearMap.id)) = 2) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, IsUnit P ∧
      t * P = P * Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) := by
  classical
  let f := Matrix.toLin' t
  have hf : ∀ v, f (f v) = v := fun v => by
    have : f (f v) = (t * t).mulVec v := by
      show Matrix.toLin' t (Matrix.toLin' t v) = _
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [this, ht, Matrix.one_mulVec]
  have hsum := involution_finrank_add h2 f hf
  have h4 : finrank F (Fin 4 → F) = 4 := by simp
  have hdim' : finrank F (LinearMap.ker (f + LinearMap.id)) = 2 := hdim
  have hb : finrank F (LinearMap.ker (f - LinearMap.id)) = 2 := by omega
  obtain ⟨B, hB1, hB2⟩ := exists_basis_involution' h2 f hf 2 2 hdim' hb
  let B' : Basis (Fin 4) F (Fin 4 → F) := B.reindex finSumFinEquiv
  let P : Matrix (Fin 4) (Fin 4) F := (Pi.basisFun F (Fin 4)).toMatrix B'
  have hP : ∀ i j, P i j = B' j i := fun i j => by
    simp [P, Basis.toMatrix_apply]
  have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
  have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
  have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
  have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide
  have c0 : t.mulVec (B' 0) = (-1 : F) • B' 0 := by
    have h := hB1 0
    have : B' 0 = B (Sum.inl 0) := by simp [B', Basis.reindex_apply, e0]
    rw [this]
    simpa [f, Matrix.toLin'_apply] using h
  have c1 : t.mulVec (B' 1) = (-1 : F) • B' 1 := by
    have h := hB1 1
    have : B' 1 = B (Sum.inl 1) := by simp [B', Basis.reindex_apply, e1]
    rw [this]
    simpa [f, Matrix.toLin'_apply] using h
  have c2 : t.mulVec (B' 2) = (1 : F) • B' 2 := by
    have h := hB2 0
    have : B' 2 = B (Sum.inr 0) := by simp [B', Basis.reindex_apply, e2]
    rw [this]
    simpa [f, Matrix.toLin'_apply] using h
  have c3 : t.mulVec (B' 3) = (1 : F) • B' 3 := by
    have h := hB2 1
    have : B' 3 = B (Sum.inr 1) := by simp [B', Basis.reindex_apply, e3]
    rw [this]
    simpa [f, Matrix.toLin'_apply] using h
  have hcol : ∀ j, t.mulVec (B' j) = ((![-1, -1, 1, 1] : Fin 4 → F) j) • B' j := by
    intro j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide +revert
    rcases hj with rfl | rfl | rfl | rfl
    · simpa using c0
    · simpa using c1
    · simpa using c2
    · simpa using c3
  refine ⟨P, ?_, ?_⟩
  · have := Basis.invertibleToMatrix (Pi.basisFun F (Fin 4)) B'
    exact isUnit_of_invertible P
  · ext i j
    have h1 : (t * P) i j = (t.mulVec (B' j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hP]
    rw [h1, hcol j]
    simp [Matrix.mul_diagonal, hP, mul_comm]

theorem involution_det {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (t : Matrix ι ι F) (ht : t * t = 1) :
    t.det = (-1) ^ finrank F (LinearMap.ker (Matrix.toLin' t + LinearMap.id)) := by
  classical
  let f := Matrix.toLin' t
  have hf : ∀ v, f (f v) = v := fun v => by
    have : f (f v) = (t * t).mulVec v := by
      show Matrix.toLin' t (Matrix.toLin' t v) = _
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [this, ht, Matrix.one_mulVec]
  obtain ⟨B, hB1, hB2⟩ := exists_basis_involution' h2 f hf _ _ rfl rfl
  have hd : LinearMap.det f = (-1) ^ finrank F (LinearMap.ker (f + LinearMap.id)) := by
    rw [← LinearMap.det_toMatrix B]
    have : LinearMap.toMatrix B B f =
        Matrix.diagonal (Sum.elim (fun _ => (-1 : F)) (fun _ => (1 : F))) := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      rcases j with j | j
      · rw [hB1 j]
        rcases eq_or_ne i (Sum.inl j) with rfl | hne
        · simp [Basis.repr_self]
        · simp [Basis.repr_self, hne]
      · rw [hB2 j]
        rcases eq_or_ne i (Sum.inr j) with rfl | hne
        · simp [Basis.repr_self]
        · simp [Basis.repr_self, hne]
    rw [this, Matrix.det_diagonal, Fintype.prod_sum_type]
    simp
  rw [← LinearMap.det_toLin' t]
  exact hd

theorem involution_dim_two {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = 4) (t : Matrix ι ι F) (ht : t * t = 1)
    (hdet : t.det = 1) (h1 : t ≠ 1) (hm1 : t ≠ -1) :
    finrank F (LinearMap.ker (Matrix.toLin' t + LinearMap.id)) = 2 := by
  classical
  let f := Matrix.toLin' t
  have hf : ∀ v, f (f v) = v := fun v => by
    have : f (f v) = (t * t).mulVec v := by
      show Matrix.toLin' t (Matrix.toLin' t v) = _
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [this, ht, Matrix.one_mulVec]
  have hsum := involution_finrank_add h2 f hf
  have h4 : finrank F (ι → F) = 4 := by rw [Module.finrank_fintype_fun_eq_card, hι]
  have hdet' := involution_det h2 t ht
  rw [hdet] at hdet'
  have hneg : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    have : (2 : F) = 1 - -1 := by norm_num
    rw [this, h]; simp
  have hev : Even (finrank F (LinearMap.ker (f + LinearMap.id))) := by
    rw [← neg_one_pow_eq_one_iff_even hneg]
    exact hdet'.symm
  set a := finrank F (LinearMap.ker (f + LinearMap.id)) with ha
  set b := finrank F (LinearMap.ker (f - LinearMap.id)) with hb
  have hab : a + b = 4 := by rw [hsum, h4]
  obtain ⟨m, hm⟩ := hev
  have hcases : a = 0 ∨ a = 2 ∨ a = 4 := by omega
  rcases hcases with h0 | h2' | h4'
  · exfalso
    have hb4 : b = 4 := by omega
    have htop : LinearMap.ker (f - LinearMap.id) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [← hb, hb4, h4])
    apply h1
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker (f - LinearMap.id) := by rw [htop]; trivial
    have : f v - v = 0 := by simpa using hv
    show f v = (Matrix.toLin' (1 : Matrix ι ι F)) v
    rw [Matrix.toLin'_apply (1 : Matrix ι ι F), Matrix.one_mulVec]
    exact sub_eq_zero.1 this
  · exact h2'
  · exfalso
    have htop : LinearMap.ker (f + LinearMap.id) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [← ha, h4']; exact h4.symm)
    apply hm1
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker (f + LinearMap.id) := by rw [htop]; trivial
    have : f v + v = 0 := by simpa using hv
    show f v = (Matrix.toLin' (-1 : Matrix ι ι F)) v
    rw [Matrix.toLin'_apply (-1 : Matrix ι ι F), Matrix.neg_mulVec, Matrix.one_mulVec]
    exact eq_neg_of_add_eq_zero_left this

end CFSG.GH74.Generic
