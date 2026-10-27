module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRootOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K]

@[expose] def kronMat (A : Matrix (Fin 3) (Fin 3) K) : Matrix Idx Idx K :=
  Matrix.fromBlocks A 0 0 (Matrix.fromBlocks A 0 0 1)

theorem kronMat_mulVec_vecOf (A : Matrix (Fin 3) (Fin 3) K) (xs ys : Fin 3 → K) (z : K) :
    kronMat A *ᵥ vecOf K xs ys z = vecOf K (A *ᵥ xs) (A *ᵥ ys) z := by
  simp only [kronMat, vecOf, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    Matrix.one_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem kronMat_one : kronMat (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  simp [kronMat]

theorem kronMat_mul (A B : Matrix (Fin 3) (Fin 3) K) :
    kronMat (A * B) = kronMat A * kronMat B := by
  simp [kronMat, Matrix.fromBlocks_multiply]

theorem dotProduct_mulVec_of_transpose_mul {A : Matrix (Fin 3) (Fin 3) K} (hA : Aᵀ * A = 1)
    (x y : Fin 3 → K) : (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hA,
    Matrix.one_mulVec]

theorem modelQuad_vecOf_eq_dotProduct (a : K) (xs ys : Fin 3 → K) (z : K) :
    modelQuad K a (vecOf K xs ys z) = xs ⬝ᵥ xs - xs ⬝ᵥ ys + ys ⬝ᵥ ys + a * z ^ 2 := by
  simp only [modelQuad_vecOf, dotProduct, Fin.sum_univ_three]
  ring

theorem modelPolar_vecOf_eq_dotProduct (a : K) (xs ys xs' ys' : Fin 3 → K) (z z' : K) :
    modelPolar K a (vecOf K xs ys z) (vecOf K xs' ys' z') =
      2 * (xs ⬝ᵥ xs') - xs ⬝ᵥ ys' - ys ⬝ᵥ xs' + 2 * (ys ⬝ᵥ ys') + 2 * a * z * z' := by
  simp only [modelPolar_vecOf, dotProduct, Fin.sum_univ_three]
  ring

theorem modelQuad_kronMat_mulVec {A : Matrix (Fin 3) (Fin 3) K} (hA : Aᵀ * A = 1) (a : K)
    (w : Idx → K) : modelQuad K a (kronMat A *ᵥ w) = modelQuad K a w := by
  rw [← vecOf_eq_self w, kronMat_mulVec_vecOf, modelQuad_vecOf_eq_dotProduct,
    modelQuad_vecOf_eq_dotProduct, dotProduct_mulVec_of_transpose_mul hA,
    dotProduct_mulVec_of_transpose_mul hA, dotProduct_mulVec_of_transpose_mul hA]

theorem kronMat_mul_rotMat_const (A : Matrix (Fin 3) (Fin 3) K) (k : ZMod 3) :
    kronMat A * rotMat K (fun _ => k) = rotMat K (fun _ => k) * kronMat A := by
  have key : ∀ (α β : K) (xs ys : Fin 3 → K),
      A *ᵥ (fun i => α * xs i + β * ys i) = fun i => α * (A *ᵥ xs) i + β * (A *ᵥ ys) i := by
    intro α β xs ys
    funext i
    simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring
  rw [Matrix.ext_iff_mulVec]
  intro w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← vecOf_eq_self w, rotMat_mulVec_vecOf,
    kronMat_mulVec_vecOf, kronMat_mulVec_vecOf, rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨?_, ?_, rfl⟩ <;> exact key _ _ _ _

@[expose] def kronHom : Matrix (Fin 3) (Fin 3) K →* Matrix Idx Idx K where
  toFun := kronMat
  map_one' := kronMat_one
  map_mul' := kronMat_mul

@[expose] def kronGL : GL (Fin 3) K →* GL Idx K := Units.map kronHom

theorem coe_kronGL (A : GL (Fin 3) K) :
    ((kronGL A : GL Idx K) : Matrix Idx Idx K) = kronMat (A : Matrix (Fin 3) (Fin 3) K) := rfl

theorem kronMat_injective :
    Function.Injective (kronMat : Matrix (Fin 3) (Fin 3) K → Matrix Idx Idx K) := by
  intro A B h
  rw [Matrix.ext_iff_mulVec]
  intro x
  have := congrArg (fun M => M *ᵥ vecOf K x 0 0) h
  simp only [kronMat_mulVec_vecOf] at this
  exact ((vecOf_eq_iff _ _ _ _ _ _).1 this).1

theorem kronGL_injective : Function.Injective (kronGL : GL (Fin 3) K →* GL Idx K) := by
  intro A B h
  apply Units.ext
  exact kronMat_injective (congrArg (fun g : GL Idx K => (g : Matrix Idx Idx K)) h)

theorem orderOf_kronGL (A : GL (Fin 3) K) : orderOf (kronGL A) = orderOf A :=
  orderOf_injective kronGL kronGL_injective A

theorem modelQuad_kronGL_mulVec {A : GL (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ * A = 1) (a : K) (w : Idx → K) :
    modelQuad K a (((kronGL A : GL Idx K) : Matrix Idx Idx K) *ᵥ w) = modelQuad K a w :=
  modelQuad_kronMat_mulVec hA a w

theorem mem_Omega7_conj_kronGL [Finite K] (F : Frame K) {A : GL (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ * A = 1) (hodd : Odd (orderOf A)) :
    F.P * kronGL A * F.P⁻¹ ∈ Omega7 K :=
  F.mem_Omega7_conj_of_odd (fun w => modelQuad_kronGL_mulVec hA F.a w)
    (by rwa [orderOf_kronGL])

@[expose] noncomputable def kronElt [Finite K] (F : Frame K) {A : GL (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ * A = 1) (hodd : Odd (orderOf A)) : ↥(Omega7 K) :=
  ⟨F.P * kronGL A * F.P⁻¹, mem_Omega7_conj_kronGL F hA hodd⟩

theorem orderOf_kronElt [Finite K] (F : Frame K) {A : GL (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ * A = 1) (hodd : Odd (orderOf A)) :
    orderOf (kronElt F hA hodd) = orderOf A := by
  rw [kronElt, orderOf_modelElt F (mem_Omega7_conj_kronGL F hA hodd), orderOf_kronGL]

theorem commute_c₀_kronElt [Finite K] (F : Frame K) {A : GL (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ * A = 1) (hodd : Odd (orderOf A)) (k : ZMod 3) :
    Commute (c₀ F (Multiplicative.ofAdd fun _ => k)) (kronElt F hA hodd) := by
  have h := mem_centralizer_c₀_of_model F (Multiplicative.ofAdd fun _ => k)
    (m := kronGL A) (mem_Omega7_conj_kronGL F hA hodd)
    (by simpa [coe_kronGL] using (kronMat_mul_rotMat_const (A : Matrix (Fin 3) (Fin 3) K) k))
  exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
