module

public import CFSG.GH74.GLS.C3.Layer2.L5C5e
public import CFSG.GH74.GLS.C3.Layer2.L5C2b

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

@[expose] def pcode2 (p : Nat × Bool) : Nat := 2 * p.1 + p.2.toNat

@[expose] def pdec2 (c : Nat) : Nat × Bool := (c / 2, decide (c % 2 = 1))

theorem pdec2_pcode2 (p : Nat × Bool) : pdec2 (pcode2 p) = p := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp [pdec2, pcode2]
  all_goals omega

theorem pcode2_pdec2 (c : Nat) : pcode2 (pdec2 c) = c := by
  simp only [pdec2, pcode2]
  by_cases h : c % 2 = 1 <;> simp [h] <;> omega

theorem pcode2_lt {p : Nat × Bool} (hp : p.1 < 128) : pcode2 p < 256 := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp [pcode2] <;> omega

theorem pdec2_lt {c : Nat} (hc : c < 256) : (pdec2 c).1 < 128 := by
  simp only [pdec2]
  omega

@[expose] def sh2Enum
    (ty : Fin 4) : Idx 256 ≃ Sh2 ty where
  toFun a := dec2 ty (pdec2 a.v)
  invFun x := ⟨⟨pcode2 (idx0 (x.fst : Perm (Fin 16)), x.snd), pcode2_lt (idx0_lt x.fst)⟩⟩
  left_inv a := by
    apply Idx.ext
    show pcode2 (idx0 (dec0 (pdec2 a.v).1 : Perm (Fin 16)), (pdec2 a.v).2) = a.v
    rw [idx0_dec0 (pdec2_lt (Idx.v_lt a))]
    exact pcode2_pdec2 a.v
  right_inv x := by
    show dec2 ty (pdec2 (pcode2 (idx0 (x.fst : Perm (Fin 16)), x.snd))) = x
    rw [pdec2_pcode2]
    exact Ext2.ext (dec0_idx0 x.fst) rfl

theorem sh2Enum_apply
    (ty : Fin 4) (a : Idx 256) : sh2Enum ty a = dec2 ty (pdec2 a.v) := rfl

theorem idxv_mk {n k : Nat} (h : k < n) : (Idx.mk ⟨k, h⟩ : Idx n).v = k := rfl

@[expose] def sh2Tab (ty : Fin 4) : Array Nat :=
  Array.ofFn (n := 256 * 256) fun k =>
    pcode2 (mul2 ty.val (pdec2 (k.val / 256)) (pdec2 (k.val % 256)))

@[expose] def sh2InvT (ty : Fin 4) : Array Nat :=
  Array.ofFn (n := 256) fun k => pcode2 (inv2 ty.val (pdec2 k.val))

theorem sh2Tab_get (ty : Fin 4) {a b : Nat} (ha : a < 256) (hb : b < 256) :
    (sh2Tab ty).getD (a * 256 + b) 0 = pcode2 (mul2 ty.val (pdec2 a) (pdec2 b)) := by
  have hk : a * 256 + b < 256 * 256 := by omega
  have h1 : (a * 256 + b) / 256 = a := by omega
  have h2 : (a * 256 + b) % 256 = b := by omega
  simp [sh2Tab, Array.getD_eq_getD_getElem?, hk, h1, h2]

theorem sh2InvT_get (ty : Fin 4) {a : Nat} (ha : a < 256) :
    (sh2InvT ty).getD a 0 = pcode2 (inv2 ty.val (pdec2 a)) := by
  simp [sh2InvT, Array.getD_eq_getD_getElem?, ha]

@[expose] def sh2TabD
    (ty : Fin 4) : TabData (Sh2 ty) where
  n := 256
  e := sh2Enum ty
  idxFn x := pcode2 (idx0 (x.fst : Perm (Fin 16)), x.snd)
  tab := sh2Tab ty
  invT := sh2InvT ty
  oneI := 0
  idxFn_spec a := by
    show pcode2 (idx0 (dec0 (pdec2 a.v).1 : Perm (Fin 16)), (pdec2 a.v).2) = a.v
    rw [idx0_dec0 (pdec2_lt (Idx.v_lt a))]
    exact pcode2_pdec2 a.v
  lt_tab a b := by
    rw [sh2Tab_get ty (Idx.v_lt a) (Idx.v_lt b)]
    exact pcode2_lt (mul2_lt ty (pdec2_lt (Idx.v_lt a)) (pdec2_lt (Idx.v_lt b)))
  tab_spec a b := by
    rw [sh2Enum_apply, sh2Enum_apply, sh2Enum_apply, idxv_mk,
      sh2Tab_get ty (Idx.v_lt a) (Idx.v_lt b), pdec2_pcode2]
    exact dec2_mul ty (pdec2_lt (Idx.v_lt a)) (pdec2_lt (Idx.v_lt b))
  lt_inv a := by
    rw [sh2InvT_get ty (Idx.v_lt a)]
    exact pcode2_lt (inv2_lt ty (pdec2_lt (Idx.v_lt a)))
  inv_spec a := by
    rw [sh2Enum_apply, sh2Enum_apply, idxv_mk, sh2InvT_get ty (Idx.v_lt a), pdec2_pcode2]
    exact dec2_inv ty (pdec2_lt (Idx.v_lt a))
  lt_one := by norm_num
  one_spec := by
    show dec2 ty (pdec2 0) = 1
    exact dec2_one ty

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
