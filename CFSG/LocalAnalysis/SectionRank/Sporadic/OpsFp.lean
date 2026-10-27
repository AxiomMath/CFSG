module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import CFSG.Sporadic.He.FpSpec
public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank

open CFSG.Sporadic.He.Native CFSG.SectionRank.Native
open scoped Matrix

theorem toVec_vecMulRow (p d : ℕ) (v : Array ℕ) (X : Array (Array ℕ)) :
    toVec p d (vecMulRow p d v X) = toVec p d v ᵥ* toMat p d X := by
  funext k
  rw [toVec_apply, Matrix.vecMul, dotProduct]
  unfold vecMulRow
  rw [getElem!_ofFn _ k.isLt, dot_cast]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold col
  rw [getElem!_ofFn _ j.isLt]
  rfl

@[expose] noncomputable def specP (p d : ℕ) : OpsSpec (opsP p d) p d where
  toMat := toMat p d
  toVec := toVec p d
  WF _ := True
  VWF _ := True
  decode_wf _ := trivial
  toMat_decode s := toMat_rowsOf p d s
  mul_wf _ _ := trivial
  toMat_mul _ _ := toMat_mulM p d _ _
  one_wf := trivial
  toMat_one := toMat_idM p d
  toMat_eq _ _ h := toMat_eq_of_beq h
  vmul_wf _ _ := trivial
  toVec_vmul _ _ := toVec_vecMulRow p d _ _
  unit_wf _ := trivial
  toVec_ne {u w} h := by
    intro e
    simp only [opsP, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
    obtain ⟨j, hj, hne⟩ := h
    have := congrFun e ⟨j, hj⟩
    rw [toVec_apply, toVec_apply, ZMod.natCast_eq_natCast_iff'] at this
    exact hne this

end CFSG.SectionRank
