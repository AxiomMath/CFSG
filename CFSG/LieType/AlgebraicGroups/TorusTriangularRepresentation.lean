module

public import CFSG.LinearAlgebra.TorusFlagBasis
public import CFSG.LieType.AlgebraicGroups.TorusCoordinates
public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti Module WithConv
open scoped TensorProduct

universe u v

theorem exists_diagonal_basis_same_flag_of_torus
    {k : Type u} [Field k] [IsAlgClosed k]
    (T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (hT : TauCeti.torusCommHopfAlgProperty k T)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k T V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := T) b).IsUpperTriangular) :
    ∃ (b' : Basis (Fin n) k V),
      (b.toMatrix b').IsUpperUnitriangular ∧ (∀ r, b'.flag r = b.flag r) ∧
      Comodule.coefficientMatrix (C := T) b' =
        Matrix.diagonal (fun i => Comodule.coefficientMatrix (C := T) b i i) := by
  classical
  obtain ⟨r,⟨e⟩⟩ := CFSG.LieType.AlgebraicGroups.exists_coordinateEquiv_of_torus T hT
  let : Comodule k (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V :=
    Comodule.Corestrict e.symm.toCoalgHom
  have hco (d : Basis (Fin n) k V) :
      Comodule.coefficientMatrix (C := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) d =
        (Comodule.coefficientMatrix (C := T) d).map e.symm :=
    Comodule.coefficientMatrix_corestrict d e.symm.toCoalgHom
  have htri' : (Comodule.coefficientMatrix (C := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) b).IsUpperTriangular := by
    rw [hco]
    intro i j hj
    simp [Matrix.map_apply, htri hj]
  obtain ⟨b',wt,hA,hflag,hdiag,hwt⟩ := CFSG.LinearAlgebra.exists_diagonal_basis_same_flag_of_upperTriangular b htri'
  refine ⟨b',hA,hflag,?_⟩
  apply Matrix.ext
  intro i j
  apply e.symm.injective
  have hh := congrArg (fun A : Matrix (Fin n) (Fin n) (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) => A i j) hdiag
  rw [hco] at hh
  by_cases hij : i = j
  · subst j
    have hw := hwt i
    rw [hco] at hw
    simp only [Matrix.diagonal_apply_eq, Matrix.map_apply] at hh hw
    rw [Matrix.diagonal_apply_eq]
    exact hh.trans hw.symm
  · simpa [Matrix.map_apply, Matrix.diagonal, hij] using hh

private theorem matrixCoefficientSubalgebra_eq_adjoin_diagonal
    {k C V : Type*} [CommRing k] [Semiring C] [Algebra k C] [Coalgebra k C]
    [AddCommMonoid V] [Module k V] [Comodule k C V] {n : ℕ}
    (b : Basis (Fin n) k V) (c : Fin n → C)
    (hco : Comodule.coefficientMatrix (C := C) b = Matrix.diagonal c) :
    Comodule.matrixCoefficientSubalgebra (R := k) (C := C) (M := V) =
      Algebra.adjoin k (Set.range c) := by
  apply le_antisymm
  · apply Comodule.matrixCoefficientSubalgebra_le
    intro φ v
    rw [Comodule.matrixCoefficient_def, Comodule.coact_eq_sum_basis_matrixCoefficient b]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
    apply Subalgebra.sum_mem
    intro i _
    have he : Comodule.matrixCoefficient (C := C) (b.coord i) v = (b.repr v i) • c i := by
      have hv := congrArg (Comodule.matrixCoefficientLinear (C := C) (b.coord i)) (b.sum_repr v)
      simp only [map_sum, map_smul, Comodule.matrixCoefficientLinear_apply] at hv
      simp_rw [← Comodule.coefficientMatrix_apply, hco] at hv
      simpa [Matrix.diagonal, Finset.sum_ite_eq, eq_comm] using hv.symm
    rw [he]
    apply Subalgebra.smul_mem
    apply Subalgebra.smul_mem
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  · apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    have hh := congrArg (fun A : Matrix (Fin n) (Fin n) C => A i i) hco
    rw [Matrix.diagonal_apply_eq] at hh
    rw [← hh, Comodule.coefficientMatrix_apply]
    exact Comodule.matrixCoefficient_mem_subalgebra _ _

private theorem adjoin_diagonal_sup_antipode_eq_top_of_torus
    {k : Type u} [Field k] [IsAlgClosed k]
    (T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (hT : TauCeti.torusCommHopfAlgProperty k T)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k T V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := T) b).IsUpperTriangular)
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := T) b)) :
    let S := Algebra.adjoin k (Set.range (fun i => Comodule.coefficientMatrix (C := T) b i i))
    S ⊔ S.map (HopfAlgebra.antipodeAlgHom k T) = ⊤ := by
  obtain ⟨b',hA,hflag,hco⟩ := exists_diagonal_basis_same_flag_of_torus T hT b htri
  have hcoef := matrixCoefficientSubalgebra_eq_adjoin_diagonal b'
    (fun i => Comodule.coefficientMatrix (C := T) b i i) hco
  have hgen := (Comodule.coordinateBialgHom_surjective_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top b).mp hfaith
  rwa [hcoef] at hgen

theorem adjoin_diagonal_antipode_eq_top_of_torus
    {k : Type u} [Field k] [IsAlgClosed k]
    (T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (hT : TauCeti.torusCommHopfAlgProperty k T)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k T V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := T) b).IsUpperTriangular)
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := T) b)) :
    Algebra.adjoin k (Set.range (fun i => Comodule.coefficientMatrix (C := T) b i i) ∪
      Set.range (fun i => HopfAlgebra.antipodeAlgHom k T
        (Comodule.coefficientMatrix (C := T) b i i))) = ⊤ := by
  have h := adjoin_diagonal_sup_antipode_eq_top_of_torus T hT b htri hfaith
  dsimp only at h
  rw [AlgHom.map_adjoin, ← Algebra.adjoin_union] at h
  have heq : (HopfAlgebra.antipodeAlgHom k T) ''
      Set.range (fun i => Comodule.coefficientMatrix (C := T) b i i) =
        Set.range (fun i => HopfAlgebra.antipodeAlgHom k T
          (Comodule.coefficientMatrix (C := T) b i i)) := by
    ext x
    constructor
    · rintro ⟨y,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨_,Set.mem_range_self i,rfl⟩
  rwa [heq] at h

theorem surjective_restriction_of_diagonal_coefficients
    {k : Type u} [Field k] [IsAlgClosed k]
    (B T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k B V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := B) b).IsUpperTriangular)
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := B) b))
    (q : B →ₐc[k] T) (hq : Function.Surjective q)
    (S : Subalgebra k B)
    (hc : ∀ i, Comodule.coefficientMatrix (C := B) b i i ∈ S)
    (hant : ∀ i, HopfAlgebra.antipodeAlgHom k B
      (Comodule.coefficientMatrix (C := B) b i i) ∈ S) :
    Function.Surjective (q.toAlgHom.comp S.val) := by
  let : Comodule k T V := Comodule.Corestrict q.toCoalgHom
  have hco : Comodule.coefficientMatrix (C := T) b =
      (Comodule.coefficientMatrix (C := B) b).map q := Comodule.coefficientMatrix_corestrict b q.toCoalgHom
  have htriT : (Comodule.coefficientMatrix (C := T) b).IsUpperTriangular := by
    rw [hco]
    intro i j hj
    simp [Matrix.map_apply,htri hj]
  have hfaithT : Function.Surjective (Comodule.coordinateBialgHom (H := T) b) := by
    rw [Comodule.coordinateBialgHom_corestrict]
    exact hq.comp hfaith
  have hgen := adjoin_diagonal_antipode_eq_top_of_torus T hT b htriT hfaithT
  have hle : Algebra.adjoin k (Set.range (fun i => Comodule.coefficientMatrix (C := T) b i i) ∪
      Set.range (fun i => HopfAlgebra.antipodeAlgHom k T
        (Comodule.coefficientMatrix (C := T) b i i))) ≤ S.map q.toAlgHom := by
    apply Algebra.adjoin_le
    rintro x (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · exact ⟨_,hc i,by rw [hco];rfl⟩
    · refine ⟨_,hant i,?_⟩
      rw [hco]
      exact BialgHomClass.map_antipode q _
  have htop : S.map q.toAlgHom = ⊤ := top_unique (hgen ▸ hle)
  rw [← AlgHom.range_eq_top]
  rw [Subalgebra.range_comp_val]
  exact htop

theorem surjective_comp_of_range_diagonal_coefficients
    {k : Type u} [Field k] [IsAlgClosed k]
    (B T D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k B V]
    {n : ℕ} (b : Basis (Fin n) k V)
    (htri : (Comodule.coefficientMatrix (C := B) b).IsUpperTriangular)
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := B) b))
    (q : B →ₐc[k] T) (hq : Function.Surjective q) (p : D →ₐc[k] B)
    (hc : ∀ i, Comodule.coefficientMatrix (C := B) b i i ∈ p.toAlgHom.range)
    (hant : ∀ i, HopfAlgebra.antipodeAlgHom k B
      (Comodule.coefficientMatrix (C := B) b i i) ∈ p.toAlgHom.range) :
    Function.Surjective (q.comp p) := by
  have hs := surjective_restriction_of_diagonal_coefficients B T hT b htri hfaith q hq
    p.toAlgHom.range hc hant
  intro t
  obtain ⟨x,hx⟩ := hs t
  obtain ⟨d,hd⟩ := x.property
  refine ⟨d,?_⟩
  change q (p d) = t
  change q x.val = t at hx
  change p d = x.val at hd
  rwa [hd]

end CFSG.LieType.AlgebraicGroups
