module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Vec

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

theorem cube_roots : ∀ c : GF64, c ^ 3 = 1 →
    c = GF64.ofNat' 1 ∨ c = GF64.ofNat' 8 ∨ c = GF64.ofNat' 9 := by
  decide +kernel

theorem cube_roots_mem : ∀ c ∈ [GF64.ofNat' 1, GF64.ofNat' 8, GF64.ofNat' 9], c ^ 3 = 1 := by
  decide +kernel

theorem norm_eq_one_of_cube {c : GF64} (hc : c ^ 3 = 1) : c * hU.bar c = 1 := by
  rw [bar_apply_eq, barC_eq_pow]
  calc c * c ^ 8 = c ^ 9 := by ring
    _ = (c ^ 3) ^ 3 := by ring
    _ = 1 := by rw [hc]; norm_num

@[expose] noncomputable def scalarGL (c : GF64) (hc : c ^ 3 = 1) : GL (Fin 3) GF64 :=
  Matrix.GeneralLinearGroup.scalar (Fin 3)
    (Units.mk0 c (by rintro rfl; simp at hc))

theorem coe_scalarGL (c : GF64) (hc : c ^ 3 = 1) :
    ((scalarGL c hc : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) = c • 1 := by
  rw [scalarGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]
  rfl

theorem scalarGL_mem (c : GF64) (hc : c ^ 3 = 1) : scalarGL c hc ∈ SU := by
  rw [mem_SU_iff', coe_scalarGL]
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_smul, Matrix.det_one]
    simp [hc]
  · have h := norm_eq_one_of_cube hc
    rw [bar_apply_eq] at h
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.mul_apply] <;>
      exact (mul_comm _ _).trans h

@[expose] noncomputable def scalarSU (c : GF64) (hc : c ^ 3 = 1) : SU :=
  ⟨scalarGL c hc, scalarGL_mem c hc⟩

theorem scalarSU_mem (c : GF64) (hc : c ^ 3 = 1) : scalarSU c hc ∈ unitaryScalars hU 3 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨Units.mk0 c hc0, ?_, ?_, ?_⟩
  · exact norm_eq_one_of_cube hc
  · exact Units.ext (by simpa using hc)
  · rfl

theorem exists_scalar_of_mem {g : SU} (hg : g ∈ unitaryScalars hU 3) :
    ∃ c : GF64, (c = GF64.ofNat' 1 ∨ c = GF64.ofNat' 8 ∨ c = GF64.ofNat' 9) ∧
      ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) = c • 1 := by
  obtain ⟨u, -, hu3, hgu⟩ := hg
  have hc : (u : GF64) ^ 3 = 1 := by simpa using congrArg (fun v : GF64ˣ => (v : GF64)) hu3
  refine ⟨u, cube_roots _ hc, ?_⟩
  rw [hgu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end CFSG.AGLEmbedding.ChevOuter.U38
