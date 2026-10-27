module

public import CFSG.HardMathSupport.U4FF.ClassKron

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix

@[expose] def kronRect {k : Type*} [Field k] {ι : Type*} [Fintype ι] (κ μ : ι → Type*)
    [∀ i, Fintype (κ i)] [∀ i, Fintype (μ i)] (z : (i : ι) → Matrix (κ i) (μ i) k) :
    Matrix ((i : ι) → κ i) ((i : ι) → μ i) k :=
  Matrix.of fun x y => ∏ i, z i (x i) (y i)

@[expose] def pureTensor {k : Type*} [Field k] {ι : Type*} [Fintype ι] (κ : ι → Type*)
    [∀ i, Fintype (κ i)] (v : (i : ι) → κ i → k) : ((i : ι) → κ i) → k :=
  fun x => ∏ i, v i (x i)

section KronRect

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι]
  {κ μ ν : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, Fintype (μ i)] [∀ i, Fintype (ν i)]

theorem kronRect_apply (z : (i : ι) → Matrix (κ i) (μ i) k) (x : (i : ι) → κ i)
    (y : (i : ι) → μ i) : kronRect κ μ z x y = ∏ i, z i (x i) (y i) := rfl

theorem pureTensor_apply (v : (i : ι) → κ i → k) (x : (i : ι) → κ i) :
    pureTensor κ v x = ∏ i, v i (x i) := rfl

theorem kronRect_mul [DecidableEq ι] (A : (i : ι) → Matrix (κ i) (μ i) k)
    (B : (i : ι) → Matrix (μ i) (ν i) k) :
    kronRect κ ν (fun i => A i * B i) = kronRect κ μ A * kronRect μ ν B :=
  CFSG.QuasithinUnique.Setup.X7a.kron_mul A B

theorem kronRect_equivariant [DecidableEq ι] (A : (i : ι) → Matrix (κ i) (μ i) k)
    (X : (i : ι) → Matrix (μ i) (μ i) k) (Y : (i : ι) → Matrix (κ i) (κ i) k)
    (h : ∀ i, A i * X i = Y i * A i) :
    kronRect κ μ A * kronDep μ X = kronDep κ Y * kronRect κ μ A := by
  have hf : (fun i => A i * X i) = fun i => Y i * A i := funext h
  calc kronRect κ μ A * kronDep μ X
      = kronRect κ μ (fun i => A i * X i) := (kronRect_mul A X).symm
    _ = kronRect κ μ (fun i => Y i * A i) := congrArg (kronRect κ μ) hf
    _ = kronDep κ Y * kronRect κ μ A := kronRect_mul Y A

theorem kronRect_mul_eq_one [DecidableEq ι] [∀ i, DecidableEq (κ i)]
    (A : (i : ι) → Matrix (κ i) (μ i) k) (B : (i : ι) → Matrix (μ i) (κ i) k)
    (h : ∀ i, A i * B i = 1) : kronRect κ μ A * kronRect μ κ B = 1 := by
  have hf : (fun i => A i * B i) = fun i => (1 : Matrix (κ i) (κ i) k) := funext h
  calc kronRect κ μ A * kronRect μ κ B
      = kronRect κ κ (fun i => A i * B i) := (kronRect_mul A B).symm
    _ = kronRect κ κ (fun i => (1 : Matrix (κ i) (κ i) k)) := congrArg (kronRect κ κ) hf
    _ = kronDep κ (fun i => (1 : Matrix (κ i) (κ i) k)) := rfl
    _ = 1 := kronDep_one

theorem kronRect_mulVec_pure [DecidableEq ι] (A : (i : ι) → Matrix (κ i) (μ i) k)
    (v : (i : ι) → μ i → k) :
    kronRect κ μ A *ᵥ pureTensor μ v = pureTensor κ (fun i => A i *ᵥ v i) := by
  funext x
  have key := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (μ i)))
    (fun i b => A i (x i) b * v i b)
  simp only [Fintype.piFinset_univ] at key
  simp only [Matrix.mulVec, dotProduct, kronRect_apply, pureTensor_apply]
  rw [key]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

theorem kronDep_mulVec_pure [DecidableEq ι] (z : (i : ι) → Matrix (κ i) (κ i) k)
    (v : (i : ι) → κ i → k) :
    kronDep κ z *ᵥ pureTensor κ v = pureTensor κ (fun i => z i *ᵥ v i) :=
  kronRect_mulVec_pure z v

theorem pureTensor_ne_zero (v : (i : ι) → κ i → k) (hv : ∀ i, v i ≠ 0) :
    pureTensor κ v ≠ 0 := by
  intro h
  have hx : ∀ i, ∃ a, v i a ≠ 0 := fun i => Function.ne_iff.mp (hv i)
  choose x hx using hx
  have h1 : pureTensor κ v x = 0 := congrFun h x
  rw [pureTensor_apply] at h1
  have h2 : ∏ i, v i (x i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hx i
  exact h2 h1

theorem kronDep_diagonal [DecidableEq ι] [∀ i, DecidableEq (κ i)] (δ : (i : ι) → κ i → k) :
    kronDep κ (fun i => Matrix.diagonal (δ i)) = Matrix.diagonal (fun x => ∏ i, δ i (x i)) := by
  ext x y
  simp only [kronDep_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem pureTensor_smul_prod (v : (i : ι) → κ i → k) (c : ι → k) :
    pureTensor κ (fun i => c i • v i) = (∏ i, c i) • pureTensor κ v := by
  funext x
  simp only [pureTensor_apply, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

end KronRect

end CFSG.HardMathSupport.U4FF
