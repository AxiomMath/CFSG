module

public import CFSG.ClassicalInvolution.AschTight.S19KTrace
public import CFSG.ClassicalInvolution.AschTight.S19KMat

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem coe_blockSL3 (A : SL(2, F)) :
    ((WeakCT.blockSL F 3 2 0 (by norm_num) A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] :=
  WeakCT.coe_blockSL_three_zero A

theorem trace_blockSL3 (A : SL(2, F)) :
    ((WeakCT.blockSL F 3 2 0 (by norm_num) A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).trace =
      (A : Matrix (Fin 2) (Fin 2) F).trace + 1 := by
  rw [coe_blockSL3, Matrix.trace_fin_three, Matrix.trace_fin_two]
  simp

@[expose] noncomputable def stdEquiv : Models.rootSL2 F (n := 3) (by norm_num) ≃* SL(2, F) :=
  (MonoidHom.ofInjective (WeakCT.blockSL_injective (K := F) (m := 3) (k := 2) (i := 0)
    (by norm_num))).symm

theorem blockSL3_stdEquiv (r : Models.rootSL2 F (n := 3) (by norm_num)) :
    WeakCT.blockSL F 3 2 0 (by norm_num) (stdEquiv r) = r := by
  have hinj := WeakCT.blockSL_injective (K := F) (m := 3) (k := 2) (i := 0) (by norm_num)
  rw [← MonoidHom.ofInjective_apply hinj]
  exact congrArg Subtype.val ((MonoidHom.ofInjective hinj).apply_symm_apply r)

theorem trace_eq_stdEquiv (r : Models.rootSL2 F (n := 3) (by norm_num)) :
    (((r : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).trace =
      ((stdEquiv r : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace + 1 := by
  conv_lhs => rw [← blockSL3_stdEquiv r]
  exact trace_blockSL3 _

theorem trace_inv_transpose {x : SL(3, F)} (hx : x ∈ Models.rootSL2 F (n := 3) (by norm_num)) :
    (((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose.trace =
      ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).trace := by
  obtain ⟨A, rfl⟩ := hx
  rw [Matrix.trace_transpose, ← map_inv, trace_blockSL3, trace_blockSL3, trace_inv]

theorem eq_one_of_mem_center_rootSL2 {x : SL(3, F)}
    (hx : x ∈ Models.rootSL2 F (n := 3) (by norm_num)) (hc : x ∈ Subgroup.center SL(3, F)) :
    x = 1 := by
  have h := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hc 2
  obtain ⟨A, rfl⟩ := hx
  have h22 : ((WeakCT.blockSL F 3 2 0 (by norm_num) A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
      2 2 = 1 := by
    rw [coe_blockSL3]
    simp
  rw [h22, map_one] at h
  exact Subtype.ext h.symm

theorem blockSL3_mem_commute {M : Matrix (Fin 3) (Fin 3) F}
    (hM : ∀ x ∈ Models.rootSL2 F (n := 3) (by norm_num),
      M * ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M) :
    IsBlockScalar M := by
  let u : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let v : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hu := hM _ ⟨u, rfl⟩
  have hv := hM _ ⟨v, rfl⟩
  rw [coe_blockSL3] at hu hv
  refine isBlockScalar_of_commute_transvections M ?_ ?_
  · convert hu using 2 <;> simp [u]
  · convert hv using 2 <;> simp [v]

theorem isBlockScalar_of_mem_centralizer {x : SL(3, F)}
    (hx : x ∈ Subgroup.centralizer (Models.rootSL2 F (n := 3) (by norm_num) : Set SL(3, F))) :
    IsBlockScalar ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
  refine blockSL3_mem_commute fun y hy => ?_
  have h := Subgroup.mem_centralizer_iff.mp hx y hy
  have h' := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
  exact h'.symm

theorem coe_rootInv_three :
    ((Models.rootInv F (n := 3) (by norm_num) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [Models.rootInv, coe_blockSL3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
