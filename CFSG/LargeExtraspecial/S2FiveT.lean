module

public import CFSG.LargeExtraspecial.S2FiveGen
public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Matrix Module OrthoF2

namespace S2

variable {m : ℕ}

theorem det_one_add_vecMulVec (a φ : Fin m → ZMod 2) :
    det (1 + vecMulVec a φ) = 1 + φ ⬝ᵥ a := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

theorem sl_ext {g h : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)}
    (e : (g : Matrix (Fin m) (Fin m) (ZMod 2)) = h) : g = h :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun e i) j

@[expose] def tv (a φ : Fin m → ZMod 2) : Matrix.SpecialLinearGroup (Fin m) (ZMod 2) :=
  if h : φ ⬝ᵥ a = 0 then ⟨1 + vecMulVec a φ, by rw [det_one_add_vecMulVec, h, add_zero]⟩ else 1

@[expose] def IsTransvection (t : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) : Prop :=
  ∃ a φ : Fin m → ZMod 2, a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧ t = tv a φ

theorem coe_tv {a φ : Fin m → ZMod 2} (h : φ ⬝ᵥ a = 0) :
    ((tv a φ : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      1 + vecMulVec a φ := by
  simp [tv, h]

theorem tv_mulVec {a φ : Fin m → ZMod 2} (h : φ ⬝ᵥ a = 0) (x : Fin m → ZMod 2) :
    ((tv a φ : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ x =
      x + (φ ⬝ᵥ x) • a := by
  rw [coe_tv h, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem cycT_eq_tv {n : ℕ} (i : Fin (n + 2)) :
    cycT i = tv (Pi.single i 1) (Pi.single (i + 1) 1) := by
  have h : (Pi.single (i + 1) 1 : Fin (n + 2) → ZMod 2) ⬝ᵥ Pi.single i 1 = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne (fin_ne_add_one i).symm]
  refine sl_ext ?_
  rw [coe_tv h, ← single_eq_single_vecMulVec_single]
  rfl

theorem isTransvection_cycT {n : ℕ} (i : Fin (n + 2)) : IsTransvection (cycT i) := by
  refine ⟨Pi.single i 1, Pi.single (i + 1) 1, fun h => ?_, fun h => ?_, ?_, cycT_eq_tv i⟩
  · have := congrFun h i
    simp at this
  · have := congrFun h (i + 1)
    simp at this
  · rw [single_dotProduct, one_mul, Pi.single_eq_of_ne (fin_ne_add_one i).symm]

end S2

end CFSG.LargeExtraspecial
