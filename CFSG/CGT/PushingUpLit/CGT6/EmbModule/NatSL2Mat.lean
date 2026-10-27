module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoThree

open CFSG.SL2MinimalFaithful Matrix

section Mat

variable {K : Type*} [Field K]

@[expose] def lowerUni (s : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def diagSL (l : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem coe_lowerUni (s : K) :
    ((lowerUni s : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; s, 1] :=
  rfl

theorem coe_diagSL (l : Kˣ) :
    ((diagSL l : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)] := rfl

theorem unipotent_mulVec (s : K) (w : Fin 2 → K) :
    ((unipotent s : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec w =
      ![w 0 + s * w 1, w 1] := by
  ext i
  fin_cases i <;> simp [coe_unipotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lowerUni_mulVec (s : K) (w : Fin 2 → K) :
    ((lowerUni s : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec w =
      ![w 0, s * w 0 + w 1] := by
  ext i
  fin_cases i <;> simp [coe_lowerUni, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem diagSL_mulVec (l : Kˣ) (w : Fin 2 → K) :
    ((diagSL l : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec w =
      ![(l : K) * w 0, ((l⁻¹ : Kˣ) : K) * w 1] := by
  ext i
  fin_cases i <;> simp [coe_diagSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem diagSL_mul_unipotent (l : Kˣ) (s : K) :
    diagSL l * unipotent s * (diagSL l)⁻¹ = unipotent ((l : K) ^ 2 * s) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [coe_diagSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.adjugate_fin_two]
  all_goals ring

theorem closure_unipotent_lowerUni :
    Subgroup.closure (Set.range (unipotent (F := K)) ∪ Set.range (lowerUni (K := K))) = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (K := K) (n := 2)]
  rw [Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  apply Subgroup.subset_closure
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · left
    refine ⟨c, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [coe_unipotent, CFSG.LinearGroups.coe_transvection]
  · right
    refine ⟨c, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [lowerUni, CFSG.LinearGroups.coe_transvection]
  · exact absurd rfl hij

theorem lowerUni_add (s t : K) : lowerUni (s + t) = lowerUni s * lowerUni t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_lowerUni, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lowerUni_zero : lowerUni (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_lowerUni]

theorem diagSL_one : diagSL (1 : Kˣ) = (1 : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagSL]

theorem diagSL_mul (l l' : Kˣ) : diagSL (l * l') = diagSL l * diagSL l' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two, _root_.mul_inv_rev, mul_comm]

@[expose] def weylSL : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_weylSL :
    ((weylSL : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

theorem weylSL_conj_lowerUni (s : K) :
    weylSL⁻¹ * lowerUni s * weylSL = unipotent (-s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, coe_lowerUni, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.adjugate_fin_two]

theorem weylSL_inv_mul_lowerUni (s : K) :
    weylSL⁻¹ * lowerUni s = unipotent (-s) * weylSL⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, coe_lowerUni, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.adjugate_fin_two]

@[expose] def diagHom : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun := diagSL
  map_one' := diagSL_one
  map_mul' := diagSL_mul

@[expose] def lowerHom : Multiplicative K →* SpecialLinearGroup (Fin 2) K where
  toFun s := lowerUni s.toAdd
  map_one' := lowerUni_zero
  map_mul' s t := lowerUni_add s.toAdd t.toAdd

end Mat

section MatHom

variable {K : Type*} [Field K]

@[expose] def matHom (m : SpecialLinearGroup (Fin 2) K) :
    Multiplicative (Fin 2 → K) →* Multiplicative (Fin 2 → K) where
  toFun w := Multiplicative.ofAdd ((m : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd w))
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem matHom_apply (m : SpecialLinearGroup (Fin 2) K) (w : Multiplicative (Fin 2 → K)) :
    matHom m w = Multiplicative.ofAdd
      ((m : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd w)) := rfl

theorem matHom_mul (a b : SpecialLinearGroup (Fin 2) K) (w : Multiplicative (Fin 2 → K)) :
    matHom (a * b) w = matHom a (matHom b w) := by
  simp only [matHom_apply, toAdd_ofAdd, Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem matHom_one (w : Multiplicative (Fin 2 → K)) : matHom 1 w = w := by
  simp [matHom_apply]

theorem matHom_eq_one_iff (m : SpecialLinearGroup (Fin 2) K) (w : Multiplicative (Fin 2 → K)) :
    matHom m w = 1 ↔ w = 1 := by
  constructor
  · intro h
    have := congrArg (matHom m⁻¹) h
    rwa [← matHom_mul, inv_mul_cancel, matHom_one, map_one] at this
  · rintro rfl
    exact map_one _

end MatHom

end CFSG.CGT.PushingUpLit.CGT6.TwoThree
