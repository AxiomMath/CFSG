module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsGen
import all CFSG.Fischer.F4
public import CFSG.Fischer.T46UnitaryBase

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open Matrix CFSG.Fischer CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.EvenSmallLie.UnitarySix.YamadaInputs

abbrev sig : F4 →+* F4 := frobenius F4 2

theorem sig_apply (c : F4) : sig c = c ^ 2 := frobenius_def 2 c

theorem sig_sig (c : F4) : sig (sig c) = c := by
  rw [sig_apply, sig_apply]
  exact F4.sq_sq c

abbrev SUJ : Subgroup (SpecialLinearGroup (Fin 6) F4) := unitarySL sig

@[expose] def rootY (i j : Fin 6) (h : i ≠ j) (a : F4) : SUJ :=
  ⟨_, transvection_mul_mem_unitarySL F4.two_eq_zero sig_sig h a⟩

@[expose] def yamGen : ℕ → SUJ
  | 0 => rootY 1 0 (by decide) 1
  | 1 => rootY 1 0 (by decide) F4.ω
  | 2 => rootY 2 1 (by decide) 1
  | 3 => rootY 2 1 (by decide) F4.ω
  | 4 => rootY 3 2 (by decide) F4.ω
  | 5 => rootY 2 0 (by decide) 1
  | 6 => rootY 2 0 (by decide) F4.ω
  | 7 => rootY 3 1 (by decide) 1
  | 8 => rootY 3 1 (by decide) F4.ω
  | 9 => rootY 3 0 (by decide) 1
  | 10 => rootY 3 0 (by decide) F4.ω
  | 11 => rootY 4 1 (by decide) F4.ω
  | 12 => rootY 4 0 (by decide) 1
  | 13 => rootY 4 0 (by decide) F4.ω
  | 14 => rootY 5 0 (by decide) F4.ω
  | 15 => rootY 1 0 (by decide) 1 * rootY 0 1 (by decide) 1 * rootY 1 0 (by decide) 1
  | 16 => rootY 2 1 (by decide) 1 * rootY 1 2 (by decide) 1 * rootY 2 1 (by decide) 1
  | 17 => rootY 3 2 (by decide) F4.ω * rootY 2 3 (by decide) F4.ω * rootY 3 2 (by decide) F4.ω
  | _ => 1

@[expose] def yamMat (k : ℕ) : Matrix (Fin 6) (Fin 6) F4 :=
  ((yamGen k : SpecialLinearGroup (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)

@[expose] def Qm : Matrix (Fin 6) (Fin 6) F4 :=
  !![F4.ω, 0, 0, 0, 0, 1; F4.ω * F4.ω, 0, 0, 0, 0, 1; 0, F4.ω, 0, 0, 1, 0;
    0, F4.ω * F4.ω, 0, 0, 1, 0; 0, 0, F4.ω, 1, 0, 0; 0, 0, F4.ω * F4.ω, 1, 0, 0]

@[expose] def Qim : Matrix (Fin 6) (Fin 6) F4 :=
  !![1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, F4.ω * F4.ω, F4.ω;
    0, 0, F4.ω * F4.ω, F4.ω, 0, 0; F4.ω * F4.ω, F4.ω, 0, 0, 0, 0]

theorem Qm_mul_Qim : Qm * Qim = 1 := by decide

theorem Qim_mul_Qm : Qim * Qm = 1 := by decide

theorem witt : Qmᵀ * Qm.map sig = antiId F4 := by decide

theorem herm_eq_dot (x y : Fin 6 → F4) : herm x y = x ⬝ᵥ (sig ∘ y) := by
  rw [herm_eq]
  simp only [dotProduct, Function.comp_apply, sig_apply]

theorem map_sig_map_sig (M : Matrix (Fin 6) (Fin 6) F4) : (M.map sig).map sig = M := by
  ext i j
  simp only [Matrix.map_apply, sig_sig]

theorem transpose_antiId_map {B : SpecialLinearGroup (Fin 6) F4} (hB : B ∈ SUJ) :
    (B : Matrix (Fin 6) (Fin 6) F4)ᵀ * antiId F4 * (B : Matrix (Fin 6) (Fin 6) F4).map sig =
      antiId F4 := by
  have h := congrArg (fun M => M.map sig) (mem_unitarySL_iff.1 hB)
  simp only [Matrix.map_mul, Matrix.transpose_map, map_sig_map_sig, antiId_map] at h
  exact h

theorem conj_transpose_mul_map {B : SpecialLinearGroup (Fin 6) F4} (hB : B ∈ SUJ) :
    (Qm * (B : Matrix (Fin 6) (Fin 6) F4) * Qim)ᵀ *
      (Qm * (B : Matrix (Fin 6) (Fin 6) F4) * Qim).map sig = 1 := by
  have h1 : Qimᵀ * antiId F4 * Qim.map sig = 1 := by
    rw [← witt, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.map_mul,
      Qm_mul_Qim, Matrix.transpose_one, Matrix.map_one sig (map_zero sig) (map_one sig),
      Matrix.one_mul]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, ← h1,
    ← transpose_antiId_map hB, ← witt]
  simp only [Matrix.mul_assoc]

theorem isIsom_conj {B : SpecialLinearGroup (Fin 6) F4} (hB : B ∈ SUJ) :
    IsIsom (Qm * (B : Matrix (Fin 6) (Fin 6) F4) * Qim) := by
  intro x y
  set M := Qm * (B : Matrix (Fin 6) (Fin 6) F4) * Qim
  have hy : sig ∘ (M *ᵥ y) = M.map sig *ᵥ (sig ∘ y) :=
    funext fun i => RingHom.map_mulVec sig M y i
  rw [herm_eq_dot, herm_eq_dot, hy, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
    dotProduct_comm, mulVec_mulVec, conj_transpose_mul_map hB, one_mulVec]

@[expose] def QGL : GL (Fin 6) F4 := ⟨Qm, Qim, Qm_mul_Qim, Qim_mul_Qm⟩

theorem conj_mem_SU0 (B : SUJ) :
    QGL * Matrix.SpecialLinearGroup.toGL (B : SpecialLinearGroup (Fin 6) F4) * QGL⁻¹ ∈ SU0 := by
  rw [mem_SU0]
  refine ⟨?_, isIsom_conj B.2⟩
  rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    (B : SpecialLinearGroup (Fin 6) F4).2, Units.val_one]

@[expose] noncomputable def conjQ : SUJ →* SU0 :=
  ((MulAut.conj QGL).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.toGL.comp SUJ.subtype)).codRestrict SU0 conj_mem_SU0

theorem coe_conjQ (B : SUJ) :
    (((conjQ B : SU0) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Qm * (B : Matrix (Fin 6) (Fin 6) F4) * Qim :=
  rfl


@[expose] noncomputable def psi0 : SUJ →* Equiv.Perm (Fin 693) := piSU.comp conjQ

theorem psi0_apply (B : SUJ) (i : Fin 693) :
    (psi0 B i).val = ptIdx ((Qm * (B : Matrix (Fin 6) (Fin 6) F4) * Qim) *ᵥ uVec i) := by
  rw [psi0, MonoidHom.comp_apply, piSU_apply, coe_conjQ]

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
