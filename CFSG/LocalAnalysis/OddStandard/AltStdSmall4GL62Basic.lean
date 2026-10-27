module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Defs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Code

public section

namespace CFSG.OddStandard.AltStdSmall4.GL62

open Code
open scoped Matrix

theorem mat_ext {M N : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext h)

theorem mat_gN : mat 4328915976 = (gN : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by decide

theorem mat_gS : mat 1796246880 = (gS : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by decide

theorem mat_gG : mat 1343259808 = (gG : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by decide

theorem mat_gW : mat 9977598093 = (gW : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by decide

theorem dg_mul_z0 (A : GL (Fin 3) (ZMod 2)) : dg A * z₀ = z₀ * dg A := by
  refine Units.ext (mat_ext fun x => ?_)
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [z0_mulVec', dg_mulVec', fst_append, snd_append, Matrix.mulVec_add]

theorem z0_mem_B₀ : z₀ ∈ B₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀)

theorem dg_mem_B₀ (A : GL (Fin 3) (ZMod 2)) : dg A ∈ B₀ :=
  Subgroup.mem_sup_left (MonoidHom.mem_range.2 ⟨A, rfl⟩)

def dgZ : Subgroup (GL (Fin 6) (ZMod 2)) where
  carrier := {g | ∃ A : GL (Fin 3) (ZMod 2), g = dg A ∨ g = dg A * z₀}
  mul_mem' := by
    rintro _ _ ⟨A, rfl | rfl⟩ ⟨A', rfl | rfl⟩
    · exact ⟨A * A', Or.inl (map_mul dg A A').symm⟩
    · exact ⟨A * A', Or.inr (by rw [map_mul, mul_assoc])⟩
    · exact ⟨A * A', Or.inr (by rw [map_mul, mul_assoc, ← dg_mul_z0 A', ← mul_assoc])⟩
    · refine ⟨A * A', Or.inl ?_⟩
      rw [map_mul, mul_assoc, ← mul_assoc z₀, ← dg_mul_z0, mul_assoc, z0_mul_self, mul_one]
  one_mem' := ⟨1, Or.inl (map_one dg).symm⟩
  inv_mem' := by
    rintro _ ⟨A, rfl | rfl⟩
    · exact ⟨A⁻¹, Or.inl (map_inv dg A).symm⟩
    · refine ⟨A⁻¹, Or.inr ?_⟩
      rw [_root_.mul_inv_rev, z0_inv, ← map_inv]
      exact (dg_mul_z0 _).symm

theorem B₀_eq_dgZ : B₀ = dgZ := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rintro _ ⟨A, rfl⟩
    exact ⟨A, Or.inl rfl⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨1, Or.inr (by rw [map_one, one_mul])⟩
  · rintro _ ⟨A, rfl | rfl⟩
    · exact dg_mem_B₀ A
    · exact B₀.mul_mem (dg_mem_B₀ A) z0_mem_B₀

theorem mem_B₀_iff_dg {g : GL (Fin 6) (ZMod 2)} :
    g ∈ B₀ ↔ ∃ A : GL (Fin 3) (ZMod 2), g = dg A ∨ g = dg A * z₀ := by
  rw [B₀_eq_dgZ]
  rfl

theorem single_castAdd (j : Fin 3) :
    (Pi.single (Fin.castAdd 3 j) (1 : ZMod 2) : Fin 6 → ZMod 2) =
      Fin.append (Pi.single j (1 : ZMod 2)) (0 : Fin 3 → ZMod 2) := by
  fin_cases j <;> decide

theorem single_natAdd (j : Fin 3) :
    (Pi.single (Fin.natAdd 3 j) (1 : ZMod 2) : Fin 6 → ZMod 2) =
      Fin.append (0 : Fin 3 → ZMod 2) (Pi.single j (1 : ZMod 2)) := by
  fin_cases j <;> decide

theorem dgMat_apply (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 6) :
    dgMat A i j = dgLin A (Pi.single j 1) i := rfl

theorem dgMat_ll (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    dgMat A (Fin.castAdd 3 i) (Fin.castAdd 3 j) = A i j := by
  rw [dgMat_apply, single_castAdd, dgLin_apply, fst_append, snd_append, Matrix.mulVec_single_one,
    Fin.append_left]
  rfl

theorem dgMat_rl (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    dgMat A (Fin.natAdd 3 i) (Fin.castAdd 3 j) = 0 := by
  rw [dgMat_apply, single_castAdd, dgLin_apply, fst_append, snd_append, Matrix.mulVec_zero,
    Fin.append_right]
  rfl

theorem dgMat_lr (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    dgMat A (Fin.castAdd 3 i) (Fin.natAdd 3 j) = 0 := by
  rw [dgMat_apply, single_natAdd, dgLin_apply, fst_append, snd_append, Matrix.mulVec_zero,
    Fin.append_left]
  rfl

theorem dgMat_rr (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    dgMat A (Fin.natAdd 3 i) (Fin.natAdd 3 j) = A i j := by
  rw [dgMat_apply, single_natAdd, dgLin_apply, fst_append, snd_append, Matrix.mulVec_single_one,
    Fin.append_right]
  rfl

end CFSG.OddStandard.AltStdSmall4.GL62
