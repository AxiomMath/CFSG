module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import CFSG.F3.Spec
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank

open CFSG.F3.Native CFSG.SectionRank.Native
open scoped Matrix

theorem V.get_lt (a : V) (j : ℕ) : a.get j < 3 := by
  unfold V.get
  split_ifs <;> omega

theorem V.val_ne_of_get_ne {a b : V} {j : ℕ} (h : a.get j ≠ b.get j) : a.val j ≠ b.val j := by
  intro e
  apply h
  unfold V.val at e
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (V.get_lt a j),
    Nat.mod_eq_of_lt (V.get_lt b j)] at e
  exact e

@[expose] noncomputable def spec3 (d : ℕ) : OpsSpec (ops3 d) 3 d where
  toMat := toMat d
  toVec v j := v.val j.val
  WF X := X.size = d ∧ RowsWF X
  VWF v := v.wf = true
  decode_wf s := ⟨by simp [ops3, rowsOf], RowsWF.rowsOf d s⟩
  toMat_decode s := toMat_rowsOf d s
  mul_wf hX hY := ⟨by simp [ops3, mul, hX.1], RowsWF.mul _ d hX.2 hY.2⟩
  toMat_mul hX hY := toMat_mul hX.1 hX.2 hY.2
  one_wf := ⟨by simp [ops3, idM], RowsWF.idM d⟩
  toMat_one := toMat_idM d
  toMat_eq _ _ h := toMat_eq_of_eqM h
  vmul_wf hv hX := V.wf_comb d _ _ hX.2 hv
  toVec_vmul {v X} hv hX := by
    funext k
    change (comb d X v).val k.val = _
    rw [V.val_comb d X v hX.2 hv, Matrix.vecMul, dotProduct,
      Finset.sum_range (fun j => v.val j * X[j]!.val k.val)]
    rfl
  unit_wf k := by simp [ops3, V.wf]
  toVec_ne {u w} h := by
    intro e
    simp only [ops3, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
    obtain ⟨j, hj, hne⟩ := h
    exact V.val_ne_of_get_ne hne (congrFun e ⟨j, hj⟩)

end CFSG.SectionRank
