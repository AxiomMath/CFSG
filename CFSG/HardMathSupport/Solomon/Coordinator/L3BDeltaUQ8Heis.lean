module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutCommon
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalHeis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
  CFSG.HardMathSupport.Timmesfeld.CrossChar.HeisAux
open scoped Fin.NatCast

variable {L : Type} [Field L]

section Defs

variable (ω : Lˣ)

@[expose] noncomputable def Xg : GL (Fin 3) L := unitaryDiagGL fun i : Fin 3 => ω ^ (i : ℕ)

@[expose] noncomputable def Pg : GL (Fin 3) L := unitaryPermGL (finRotate 3)⁻¹

theorem coe_Xg : ((Xg ω : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = hX (ω : L) := by
  simp [Xg, coe_unitaryDiagGL, hX, Units.val_pow_eq_pow_val]

theorem coe_Pg : ((Pg : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = hP := by
  ext i j
  rw [Pg, coe_unitaryPermGL, permMatrix_apply']
  simp only [hP, Matrix.of_apply]
  have : ((finRotate 3)⁻¹ i = j) ↔ i = j + 1 := by
    rw [Equiv.Perm.inv_eq_iff_eq, finRotate_apply]
  simp only [this]

theorem Xg_pow_three (hω3 : ω ^ 3 = 1) : (Xg ω : GL (Fin 3) L) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_Xg, hX_pow_three (by simpa using congrArg Units.val hω3)]
  rfl

theorem Pg_pow_three : (Pg : GL (Fin 3) L) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_Pg, hP_pow_three]
  rfl

theorem Xg_mul_Pg (hω3 : ω ^ 3 = 1) :
    (Xg ω : GL (Fin 3) L) * Pg = Pg * Xg ω * GeneralLinearGroup.scalar (Fin 3) ω := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_Xg, coe_Pg,
    hX_mul_hP (by simpa using congrArg Units.val hω3), GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.smul_eq_mul_diagonal]

variable (h₀ : UnitaryFieldData 2 1 L)

theorem Xg_mem (hω3 : ω ^ 3 = 1) :
    (Xg ω : GL (Fin 3) L) ∈ gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
  refine unitaryDiagGL_mem_gramSU h₀ (fun i => ?_) ?_
  · rw [h₀.norm_eq_pow, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]
    have : (ω : L) ^ 3 = 1 := by simpa using congrArg Units.val hω3
    norm_num [this]
  · simp only [Fin.prod_univ_three, Units.val_pow_eq_pow_val]
    have : (ω : L) ^ 3 = 1 := by simpa using congrArg Units.val hω3
    simp
    calc (ω : L) * (ω : L) ^ 2 = (ω : L) ^ 3 := by ring
      _ = 1 := this

theorem Pg_mem :
    (Pg : GL (Fin 3) L) ∈ gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) :=
  unitaryPermGL_mem_gramSU h₀ (by simp)

end Defs

end CFSG.HardMathSupport.Solomon.Coordinator
