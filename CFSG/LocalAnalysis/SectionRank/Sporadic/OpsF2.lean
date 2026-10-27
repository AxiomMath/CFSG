module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native
open scoped Matrix

@[expose] noncomputable def spec2 (d : ℕ) : OpsSpec (ops2 d) 2 d where
  toMat := rowsMatrix d
  toVec := toVecD d
  WF _ := True
  VWF _ := True
  decode_wf _ := trivial
  toMat_decode s := rowsMatrix_rowsOfPayload d s
  mul_wf _ _ := trivial
  toMat_mul _ _ := rowsMatrix_mulRows d _ _
  one_wf := trivial
  toMat_one := rowsMatrix_idRows d
  toMat_eq _ _ h := by rw [beq_iff_eq.1 h]
  vmul_wf _ _ := trivial
  toVec_vmul _ _ := toVecD_vecMulN d _ _
  unit_wf _ := trivial
  toVec_ne {u w} h := by
    intro e
    simp only [ops2, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
    obtain ⟨j, hj, hne⟩ := h
    have := congrFun e ⟨j, hj⟩
    simp only [toVecD_apply] at this
    cases hu : u.testBit j <;> cases hw : w.testBit j <;> simp_all

end CFSG.SectionRank
