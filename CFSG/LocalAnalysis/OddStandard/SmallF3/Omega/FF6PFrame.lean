module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesDecomp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}

structure PFrame (Q : QuadraticForm (ZMod 3) V) (ι : Type) [Fintype ι] (c : ι → ZMod 3) where
  b : Module.Basis ι (ZMod 3) V
  norm : ∀ i, Q (b i) = c i
  orth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0

theorem PFrame.map_eq (fr : PFrame Q ι c) (x : V) : Q x = ∑ i, c i * (fr.b.repr x i) ^ 2 := by
  have hortho : (QuadraticMap.associated (R := ZMod 3) Q).IsOrthoᵢ fr.b := by
    intro i j hij
    show QuadraticMap.associated (R := ZMod 3) Q (fr.b i) (fr.b j) = 0
    rw [QuadraticMap.associated_apply]
    have h := fr.orth i j hij
    rw [QuadraticMap.polar] at h
    rw [h, smul_zero]
  have h := congrArg (fun R => R (fr.b.equivFun x))
    (QuadraticMap.basisRepr_eq_of_iIsOrtho Q fr.b hortho)
  simp only [QuadraticMap.basisRepr_apply, Module.Basis.sum_equivFun,
    QuadraticMap.weightedSumSquares_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fr.norm i, smul_eq_mul, Module.Basis.equivFun_apply, _root_.sq]

private theorem PFrame.repr_signChange_aux (fr : PFrame Q ι c) (J : Finset ι)
    {σ : V ≃ₗ[ZMod 3] V}
    (hσ : ∀ i, σ (fr.b i) = if i ∈ J then -fr.b i else fr.b i) (x : V) (i : ι) :
    fr.b.repr (σ x) i = if i ∈ J then -(fr.b.repr x i) else fr.b.repr x i := by
  let g : V →ₗ[ZMod 3] (ι → ZMod 3) :=
    { toFun := fun x i => fr.b.repr (σ x) i
      map_add' := by intro x y; funext i; simp
      map_smul' := by intro a x; funext i; simp }
  let h : V →ₗ[ZMod 3] (ι → ZMod 3) :=
    { toFun := fun x i => if i ∈ J then -(fr.b.repr x i) else fr.b.repr x i
      map_add' := by intro x y; funext i; by_cases hi : i ∈ J <;> simp [hi] <;> ring
      map_smul' := by intro a x; funext i; by_cases hi : i ∈ J <;> simp [hi] <;> ring }
  have hgh : g = h := by
    apply fr.b.ext
    intro j
    funext i
    change fr.b.repr (σ (fr.b j)) i =
      (if i ∈ J then -(fr.b.repr (fr.b j) i) else fr.b.repr (fr.b j) i)
    rw [hσ j]
    by_cases hj : j ∈ J <;> by_cases hi : i ∈ J <;> by_cases hij : i = j <;>
      simp [hj, hi, hij, Module.Basis.repr_self, Finsupp.single_eq_same, Finsupp.single_eq_of_ne,
        Finsupp.neg_apply, Ne.symm, eq_comm, neg_zero]
  exact congrFun (congrArg (fun F : V →ₗ[ZMod 3] (ι → ZMod 3) => F x) hgh) i

theorem PFrame.exists_signChange (fr : PFrame Q ι c) (J : Finset ι) :
    ∃ σ : OGroup Q, ∀ i, (σ : V ≃ₗ[ZMod 3] V) (fr.b i) = if i ∈ J then -fr.b i else fr.b i := by
  let f : V →ₗ[ZMod 3] V := fr.b.constr (ZMod 3) fun i => if i ∈ J then -fr.b i else fr.b i
  have hff : f.comp f = (LinearMap.id : V →ₗ[ZMod 3] V) := by
    apply fr.b.ext
    intro i
    show f (f (fr.b i)) = fr.b i
    rw [Module.Basis.constr_basis]
    by_cases hi : i ∈ J
    · rw [if_pos hi, map_neg, Module.Basis.constr_basis, if_pos hi, neg_neg]
    · rw [if_neg hi, Module.Basis.constr_basis, if_neg hi]
  have hf : Function.Involutive f := fun x => by
    have h := DFunLike.congr_fun hff x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  let σ : V ≃ₗ[ZMod 3] V := LinearEquiv.ofInvolutive f hf
  have hσ : ∀ i, σ (fr.b i) = if i ∈ J then -fr.b i else fr.b i := by
    intro i
    change f (fr.b i) = if i ∈ J then -fr.b i else fr.b i
    rw [Module.Basis.constr_basis]
  have hcoord : ∀ x i, fr.b.repr (σ x) i =
      if i ∈ J then -(fr.b.repr x i) else fr.b.repr x i :=
    fun x i => PFrame.repr_signChange_aux fr J hσ x i
  have hmem : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [fr.map_eq (σ x), fr.map_eq x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoord x i]
    by_cases hi : i ∈ J <;> simp [hi]
  exact ⟨⟨σ, hmem⟩, hσ⟩

noncomputable def PFrame.signChange (fr : PFrame Q ι c) (J : Finset ι) : OGroup Q :=
  Classical.choose (fr.exists_signChange J)

theorem PFrame.signChange_basis (fr : PFrame Q ι c) (J : Finset ι) (i : ι) :
    ((fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b i) =
      if i ∈ J then -fr.b i else fr.b i :=
  Classical.choose_spec (fr.exists_signChange J) i

theorem PFrame.repr_signChange (fr : PFrame Q ι c) (J : Finset ι) (x : V) (i : ι) :
    fr.b.repr (((fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) x) i =
      if i ∈ J then -(fr.b.repr x i) else fr.b.repr x i :=
  PFrame.repr_signChange_aux fr J (fr.signChange_basis J) x i

theorem PFrame.signChange_mul (fr : PFrame Q ι c) (J K : Finset ι) :
    fr.signChange J * fr.signChange K = fr.signChange (symmDiff J K) := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [Submonoid.coe_mul, LinearEquiv.mul_apply, fr.signChange_basis K i]
  by_cases hiK : i ∈ K <;> by_cases hiJ : i ∈ J <;>
    simp [hiK, hiJ, fr.signChange_basis J i, fr.signChange_basis (symmDiff J K) i,
      Finset.mem_symmDiff]

theorem PFrame.signChange_empty (fr : PFrame Q ι c) : fr.signChange ∅ = 1 := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [fr.signChange_basis ∅ i]
  simp

theorem PFrame.signChange_mul_self (fr : PFrame Q ι c) (J : Finset ι) :
    fr.signChange J * fr.signChange J = 1 := by
  rw [fr.signChange_mul, symmDiff_self, Finset.bot_eq_empty, fr.signChange_empty]

theorem PFrame.signChange_comm (fr : PFrame Q ι c) (J K : Finset ι) :
    fr.signChange J * fr.signChange K = fr.signChange K * fr.signChange J := by
  rw [fr.signChange_mul, fr.signChange_mul, symmDiff_comm]

end CFSG.OddStandard.SmallF3.Omega
