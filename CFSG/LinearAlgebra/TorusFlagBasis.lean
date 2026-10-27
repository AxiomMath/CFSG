module

public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

public noncomputable section

namespace CFSG.LinearAlgebra

open TauCeti Module WithConv
open scoped TensorProduct

universe u v

private theorem weightProj_sub_mem_flag
    {k : Type u} [Field k] {G : Type v} [Monoid G] [DecidableEq G]
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k (MonoidAlgebra k G) V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := MonoidAlgebra k G) b).IsUpperTriangular)
    (wt : Fin n → G)
    (hdiag : ∀ i, Comodule.coefficientMatrix (C := MonoidAlgebra k G) b i i =
      MonoidAlgebra.single (wt i) 1) (i : Fin n) :
    Comodule.weightProj k G V (wt i) (b i) - b i ∈ b.flag i.castSucc := by
  let N := Comodule.flagSubcomodule (H := MonoidAlgebra k G) b htri i.castSucc
  let : Comodule k (MonoidAlgebra k G) (V ⧸ N.toSubmodule) := N.instComoduleQuotient
  have hco := (Comodule.coefficientMatrix_isUpperTriangular_and_diag_iff b
    (fun i => MonoidAlgebra.single (wt i) 1)).mp ⟨htri,hdiag⟩ i
  have hweight : N.mkQ (b i) ∈ Comodule.weightSpace k G (V ⧸ N.toSubmodule) (wt i) := by
    rw [Comodule.mem_weightSpace]
    change N.quotientCoact (N.mkQ (b i)) = _
    rw [Subcomodule.mkQ_apply, Subcomodule.quotientCoact_mk, Comodule.flagSubcomodule_toSubmodule]
    exact hco
  have hmap := (N.mkQ).map_weightProj (wt i) (b i)
  rw [Comodule.weightProj_of_mem hweight] at hmap
  rw [← Comodule.flagSubcomodule_toSubmodule b htri i.castSucc]
  apply (N.mkQ_eq_zero_iff _).mp
  change N.mkQ (Comodule.weightProj k G V (wt i) (b i) - b i) = 0
  change N.toSubmodule.mkQ (_ - _) = 0
  rw [map_sub]
  change N.mkQ (Comodule.weightProj k G V (wt i) (b i)) - N.mkQ (b i) = 0
  rw [hmap, sub_self]

private theorem exists_weight_basis_adapted
    {k : Type u} [Field k] {G : Type v} [Monoid G] [DecidableEq G]
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k (MonoidAlgebra k G) V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := MonoidAlgebra k G) b).IsUpperTriangular)
    (wt : Fin n → G)
    (hdiag : ∀ i, Comodule.coefficientMatrix (C := MonoidAlgebra k G) b i i =
      MonoidAlgebra.single (wt i) 1) :
    ∃ b' : Basis (Fin n) k V,
      (∀ i, b' i ∈ Comodule.weightSpace k G V (wt i)) ∧
      (∀ i, b' i - b i ∈ b.flag i.castSucc) ∧
      (b.toMatrix b').IsUpperUnitriangular := by
  classical
  let v : Fin n → V := fun i => Comodule.weightProj k G V (wt i) (b i)
  have hv (i) : v i - b i ∈ b.flag i.castSucc := weightProj_sub_mem_flag b htri wt hdiag i
  let A : Matrix (Fin n) (Fin n) k := fun i j => b.repr (v j) i
  have hA : A.IsUpperUnitriangular := by
    rw [Matrix.isUpperUnitriangular_def]
    constructor
    · intro i j hji
      have hzero := (b.mem_flag_iff_repr_eq_zero.mp (hv j)) i (by exact_mod_cast hji.le)
      rw [map_sub, Finsupp.sub_apply, b.repr_self_apply, if_neg (by
        intro hij
        exact hji.ne (by simpa using hij)), sub_zero] at hzero
      exact hzero
    · intro i
      have hzero := (b.mem_flag_iff_repr_eq_zero.mp (hv i)) i le_rfl
      rw [map_sub, Finsupp.sub_apply, b.repr_self_apply, if_pos rfl] at hzero
      exact sub_eq_zero.mp hzero
  let e : V ≃ₗ[k] V := Matrix.toLinearEquiv b A hA.isUnit_det
  have he (i) : e (b i) = v i := by
    rw [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
    exact b.sum_repr (v i)
  let b' := b.map e
  have hb' (i) : b' i = v i := he i
  refine ⟨b', ?_, ?_, ?_⟩
  · intro i
    rw [hb']
    exact Comodule.weightProj_mem_weightSpace _ _
  · intro i
    rw [hb']
    exact hv i
  · change Matrix.IsUpperUnitriangular (fun i j => b.repr (b' j) i)
    simp_rw [hb']
    exact hA

theorem flag_eq_of_sub_mem_flag
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {n : ℕ}
    (b b' : Basis (Fin n) k V) (hb : ∀ i, b' i - b i ∈ b.flag i.castSucc) :
    ∀ r : Fin (n + 1), b'.flag r = b.flag r := by
  let : Module.Finite k V := Module.Finite.of_basis b
  have hle (r : Fin (n + 1)) : b'.flag r ≤ b.flag r := by
    rw [b'.flag_le_iff]
    intro i hi
    have hd := b.flag_mono hi.le (hb i)
    have hs := b.self_mem_flag hi
    have hh := Submodule.add_mem (b.flag r) hd hs
    simpa only [sub_add_cancel] using hh
  intro r
  apply Submodule.eq_of_le_of_finrank_eq (hle r)
  have heq (c : Basis (Fin n) k V) : Module.finrank k (c.flag r) = r.val := by
    have hspan : c.flag r = Submodule.span k
        (c '' {i : Fin n | i.castSucc < r}) := rfl
    have hcard : Fintype.card {i : Fin n // i.castSucc < r} = r.val := by
      let e : {i : Fin n // i.castSucc < r} ≃ Fin r.val :=
        { toFun := fun i => ⟨i.val.val, i.property⟩
          invFun := fun i => ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ r.isLt)⟩, i.isLt⟩
          left_inv := fun i => rfl
          right_inv := fun i => rfl }
      exact (Fintype.card_congr e).trans (Fintype.card_fin _)
    have himage : c '' {i : Fin n | i.castSucc < r} =
        Set.range (fun i : {i : Fin n // i.castSucc < r} => c i.val) := by
      ext v
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.property, rfl⟩
    have hLI : LinearIndependent k (fun i : {i : Fin n // i.castSucc < r} => c i.val) :=
      (c.linearIndepOn {i : Fin n | i.castSucc < r}).linearIndependent
    rw [hspan, himage]
    exact (finrank_span_eq_card hLI).trans hcard
  rw [heq, heq]

private theorem exists_diagonal_basis_same_flag
    {k : Type u} [Field k] {G : Type v} [Monoid G] [DecidableEq G]
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k (MonoidAlgebra k G) V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := MonoidAlgebra k G) b).IsUpperTriangular)
    (wt : Fin n → G)
    (hdiag : ∀ i, Comodule.coefficientMatrix (C := MonoidAlgebra k G) b i i =
      MonoidAlgebra.single (wt i) 1) :
    ∃ b' : Basis (Fin n) k V,
      (b.toMatrix b').IsUpperUnitriangular ∧ (∀ r, b'.flag r = b.flag r) ∧
      Comodule.coefficientMatrix (C := MonoidAlgebra k G) b' =
        Matrix.diagonal (fun i => MonoidAlgebra.single (wt i) 1) := by
  classical
  obtain ⟨b',hwt,hsub,hA⟩ := exists_weight_basis_adapted b htri wt hdiag
  refine ⟨b',hA,flag_eq_of_sub_mem_flag b b' hsub,?_⟩
  apply Matrix.ext
  intro i j
  rw [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def,
    Comodule.mem_weightSpace.mp (hwt j)]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
    Basis.coord_apply, b'.repr_self_apply]
  by_cases hij : j = i
  · subst j
    simp
  · simp [Matrix.diagonal, hij, Ne.symm hij]

private theorem isGroupLikeElem_diagonal_of_upperTriangular
    {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k C V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := C) b).IsUpperTriangular) (i : Fin n) :
    IsGroupLikeElem k (Comodule.coefficientMatrix (C := C) b i i) := by
  refine ⟨?_, ?_⟩
  · simp [Comodule.counit_coefficientMatrix]
  · rw [Comodule.comul_coefficientMatrix_eq_sum]
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hj | hj
      · rw [htri hj, TensorProduct.zero_tmul]
      · rw [htri hj, TensorProduct.tmul_zero]
    · simp

theorem exists_diagonal_basis_same_flag_of_upperTriangular
    {k : Type u} [Field k] {G : Type v} [Monoid G] [DecidableEq G]
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k (MonoidAlgebra k G) V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := MonoidAlgebra k G) b).IsUpperTriangular) :
    ∃ (b' : Basis (Fin n) k V) (wt : Fin n → G),
      (b.toMatrix b').IsUpperUnitriangular ∧ (∀ r, b'.flag r = b.flag r) ∧
      Comodule.coefficientMatrix (C := MonoidAlgebra k G) b' =
        Matrix.diagonal (fun i => MonoidAlgebra.single (wt i) 1) ∧
      (∀ i, Comodule.coefficientMatrix (C := MonoidAlgebra k G) b i i =
        MonoidAlgebra.single (wt i) 1) := by
  classical
  have hw (i) : ∃ g : G, Comodule.coefficientMatrix (C := MonoidAlgebra k G) b i i =
      MonoidAlgebra.single g 1 := by
    have hg := isGroupLikeElem_diagonal_of_upperTriangular b htri i
    obtain ⟨g,hg⟩ := (MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one.mp hg)
    exact ⟨g,hg.symm⟩
  choose wt hwt using hw
  obtain ⟨b',hA,hflag,hco⟩ := exists_diagonal_basis_same_flag b htri wt hwt
  exact ⟨b',wt,hA,hflag,hco,hwt⟩


end CFSG.LinearAlgebra
