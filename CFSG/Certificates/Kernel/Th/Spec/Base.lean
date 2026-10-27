
module

public import CFSG.Certificates.Kernel.Th.Spec.Seed
public import CFSG.Certificates.Kernel.Th.S.BaseS
public import CFSG.Sporadic.Th.BaseBase

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.Sporadic.Th CFSG.Sporadic.Th.FormBase
open scoped Matrix

section Locality

variable {code code' : Nat → Nat → Nat}

theorem expand_congr (u : Nat) : ∀ (vs : List Nat) (vis : Nat),
    (∀ v ∈ vs, code u v = code' u v) → expand code u vs vis = expand code' u vs vis
  | [], _, _ => rfl
  | v :: vs, vis, h => by
    have hv : code u v = code' u v := h v List.mem_cons_self
    have ih : ∀ vis, expand code u vs vis = expand code' u vs vis := fun vis =>
      expand_congr u vs vis fun w hw => h w (List.mem_cons_of_mem _ hw)
    simp only [expand, hv, ih]

theorem mem_expand (u : Nat) : ∀ (vs : List Nat) (vis : Nat) {v : Nat},
    v ∈ (expand code u vs vis).1 → v ∈ vs
  | [], _, v, hv => by simp [expand] at hv
  | w :: vs, vis, v, hv => by
    simp only [expand] at hv
    split at hv
    · rcases List.mem_cons.1 hv with rfl | hv
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_expand u vs _ hv)
    · exact List.mem_cons_of_mem _ (mem_expand u vs _ hv)

theorem bfsLoop_congr {m : Nat} (h : ∀ i j, i < m → j < m → code i j = code' i j) (full : Nat) :
    ∀ (fuel : Nat) (queue : List Nat) (vis : Nat) (acc : List (Nat × Nat)),
      (∀ u ∈ queue, u < m) →
      bfsLoop code (List.range m) full fuel queue vis acc =
        bfsLoop code' (List.range m) full fuel queue vis acc
  | 0, _, _, _, _ => rfl
  | _ + 1, [], _, _, _ => rfl
  | fuel + 1, u :: queue, vis, acc, hq => by
    have hu : u < m := hq u List.mem_cons_self
    have he : expand code u (List.range m) vis = expand code' u (List.range m) vis :=
      expand_congr u _ vis fun v hv => h u v hu (List.mem_range.1 hv)
    simp only [bfsLoop, he]
    split
    · rfl
    · refine bfsLoop_congr h full fuel _ _ _ fun w hw => ?_
      rcases List.mem_append.1 hw with hw | hw
      · exact hq w (List.mem_cons_of_mem _ hw)
      · exact List.mem_range.1 (mem_expand u _ vis hw)

theorem bfsLoop_parent_lt {m : Nat} (full : Nat) :
    ∀ (fuel : Nat) (queue : List Nat) (vis : Nat) (acc : List (Nat × Nat)),
      (∀ u ∈ queue, u < m) → (∀ e ∈ acc, e.2 < m) →
      ∀ e ∈ bfsLoop code (List.range m) full fuel queue vis acc, e.2 < m
  | 0, _, _, acc, _, ha, e, he => by
    simp only [bfsLoop, List.mem_reverse] at he
    exact ha e he
  | _ + 1, [], _, acc, _, ha, e, he => by
    simp only [bfsLoop, List.mem_reverse] at he
    exact ha e he
  | fuel + 1, u :: queue, vis, acc, hq, ha, e, he => by
    have hu : u < m := hq u List.mem_cons_self
    simp only [bfsLoop] at he
    split at he
    · rw [List.mem_reverse] at he
      exact ha e he
    · refine bfsLoop_parent_lt full fuel _ _ _ (fun w hw => ?_) (fun f hf => ?_) e he
      · rcases List.mem_append.1 hw with hw | hw
        · exact hq w (List.mem_cons_of_mem _ hw)
        · exact List.mem_range.1 (mem_expand u _ vis hw)
      · rcases List.mem_append.1 hf with hf | hf
        · obtain ⟨v, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hf)
          exact hu
        · exact ha f hf

theorem propagate_congr {m : Nat} (h : ∀ i j, i < m → j < m → code i j = code' i j) :
    ∀ (tree st : List (Nat × Nat)), (∀ e ∈ tree, e.2 < m) →
      propagate m code tree st = propagate m code' tree st
  | [], _, _ => rfl
  | (v, p) :: rest, st, ht => by
    have hp : p < m := ht (v, p) List.mem_cons_self
    have ih : ∀ st, propagate m code rest st = propagate m code' rest st := fun st =>
      propagate_congr h rest st fun e he => ht e (List.mem_cons_of_mem _ he)
    by_cases hv : v < m
    · have hc : code p v = code' p v := h p v hp hv
      simp only [propagate, hc, ih]
    · simp [propagate, hv]

theorem propagate_keys_lt {m : Nat} : ∀ (tree st st' : List (Nat × Nat)),
    propagate m code tree st = .ok st' → (∀ e ∈ st, e.1 < m) → ∀ e ∈ st', e.1 < m
  | [], st, st', h, hst => by
    simp only [propagate, Outcome.ok.injEq] at h
    subst h
    exact hst
  | (v, p) :: rest, st, st', h, hst => by
    simp only [propagate] at h
    split at h
    · rename_i hvm
      have hv : v < m := by simpa using (Bool.and_eq_true_iff.1 hvm).1
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i t ht
          refine propagate_keys_lt rest _ st' h (fun e he => ?_)
          rcases List.mem_cons.1 he with rfl | he
          · exact hv
          · exact hst e he
    · simp at h

theorem allEqs_congr {m : Nat} (h : ∀ i j, i < m → j < m → code i j = code' i j)
    {st : List (Nat × Nat)} (hst : ∀ e ∈ st, e.1 < m) : allEqs code st = allEqs code' st := by
  unfold allEqs
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  refine forall₂_congr fun e he => forall₂_congr fun f hf => ?_
  rw [h e.1 f.1 (hst e he) (hst f hf)]

theorem candidateOK_congr {m : Nat} (h0 : 0 < m)
    (h : ∀ i j, i < m → j < m → code i j = code' i j) {tree : List (Nat × Nat)}
    (ht : ∀ e ∈ tree, e.2 < m) (s0 : Nat) :
    candidateOK m code tree s0 = candidateOK m code' tree s0 := by
  unfold candidateOK
  rw [propagate_congr h tree _ ht]
  rcases hp : propagate m code' tree [(0, s0)] with _ | _ | st
  · rfl
  · rfl
  · have hk := propagate_keys_lt tree _ st hp (fun e he => by
      rw [List.mem_singleton] at he
      rw [he]
      exact h0)
    simp only [allEqs_congr h hk]

theorem formBaseCheck_congr {m : Nat} (h : ∀ i j, i < m → j < m → code i j = code' i j) :
    formBaseCheck m code = formBaseCheck m code' := by
  by_cases hm : 0 < m
  · have ht : bfsTree m code = bfsTree m code' :=
      bfsLoop_congr h _ _ _ _ _ fun u hu => by
        rw [List.mem_singleton] at hu
        rw [hu]
        exact hm
    have hp : ∀ e ∈ bfsTree m code, e.2 < m := by
      refine bfsLoop_parent_lt _ _ _ _ _ (fun u hu => ?_) (fun e he => by simp at he)
      rw [List.mem_singleton] at hu
      rw [hu]
      exact hm
    have hall : (List.range 16).all (candidateOK m code (bfsTree m code)) =
        (List.range 16).all (candidateOK m code' (bfsTree m code')) := by
      rw [← ht]
      exact congrArg _ (funext fun s0 => candidateOK_congr hm h hp s0)
    show (decide (0 < m) && treeCovers m (bfsTree m code) &&
        (List.range 16).all (candidateOK m code (bfsTree m code))) =
      (decide (0 < m) && treeCovers m (bfsTree m code') &&
        (List.range 16).all (candidateOK m code' (bfsTree m code')))
    rw [hall, ht]
  · have : m = 0 := by omega
    subst this
    simp [formBaseCheck]

end Locality

theorem keyRows_cons (k : Native.Key) (l : List Native.Key) :
    BaseS.keyRows (k :: l) = k.u :: k.v :: BaseS.keyRows l := rfl

theorem keyRows_nil : BaseS.keyRows ([] : List Native.Key) = [] := rfl

theorem getElem?_keyRows_two_mul : ∀ (l : List Native.Key) (i : Nat),
    (BaseS.keyRows l)[2 * i]? = l[i]?.map Native.Key.u
  | [], i => by simp [keyRows_nil]
  | k :: l, 0 => by simp [keyRows_cons]
  | k :: l, i + 1 => by
    rw [keyRows_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_cons_succ, getElem?_keyRows_two_mul l i, List.getElem?_cons_succ]

theorem getElem?_keyRows_two_mul_add_one : ∀ (l : List Native.Key) (i : Nat),
    (BaseS.keyRows l)[2 * i + 1]? = l[i]?.map Native.Key.v
  | [], i => by simp [keyRows_nil]
  | k :: l, 0 => by simp [keyRows_cons]
  | k :: l, i + 1 => by
    rw [keyRows_cons, show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_cons_succ, getElem?_keyRows_two_mul_add_one l i, List.getElem?_cons_succ]

theorem deltaKeys_size : Native.deltaKeys.size = 124 := by decide

theorem deltaRows_getD_two_mul {i : Nat} (hi : i < 124) :
    (BaseS.deltaRows.toArray[2 * i]?).getD Native.V4.zero = (Native.deltaKeys[i]!).u := by
  have hi' : i < Native.deltaKeys.size := by rw [deltaKeys_size]; exact hi
  rw [List.getElem?_toArray, BaseS.deltaRows, getElem?_keyRows_two_mul, Array.getElem?_toList,
    Array.getElem?_eq_getElem hi', getElem!_pos Native.deltaKeys i hi', Option.map_some,
    Option.getD_some]

theorem deltaRows_getD_two_mul_add_one {i : Nat} (hi : i < 124) :
    (BaseS.deltaRows.toArray[2 * i + 1]?).getD Native.V4.zero = (Native.deltaKeys[i]!).v := by
  have hi' : i < Native.deltaKeys.size := by rw [deltaKeys_size]; exact hi
  rw [List.getElem?_toArray, BaseS.deltaRows, getElem?_keyRows_two_mul_add_one,
    Array.getElem?_toList, Array.getElem?_eq_getElem hi', getElem!_pos Native.deltaKeys i hi',
    Option.map_some, Option.getD_some]

theorem rowsMatrix_deltaRows_apply {i : Nat} (hi : i < 124) (a : Fin 2) (k : Fin 248) :
    rowsMatrix BaseS.deltaRows.toArray ⟨2 * i + a.val, by omega⟩ k =
      keyVec (Native.deltaKeys[i]!) a k := by
  rw [rowsMatrix_apply]
  fin_cases a
  · simp only [Fin.zero_eta, Fin.val_zero, Nat.add_zero, keyVec_zero]
    rw [deltaRows_getD_two_mul hi]
  · simp only [Fin.mk_one, Fin.val_one, keyVec_one]
    rw [deltaRows_getD_two_mul_add_one hi]

theorem cRows_eq_deltaRows : Native.cRows () = BaseS.deltaRows.toArray := by
  refine Array.ext_getElem? fun i => ?_
  have hR : BaseS.deltaRows.toArray[i]? = BaseS.deltaRows[i]? := List.getElem?_toArray
  rw [hR, BaseS.deltaRows]
  obtain ⟨q, rfl | rfl⟩ : ∃ q, i = 2 * q ∨ i = 2 * q + 1 := ⟨i / 2, by omega⟩
  · rw [getElem?_keyRows_two_mul, Array.getElem?_toList]
    by_cases hq : q < Native.deltaKeys.size
    · have e1 : Native.deltaKeys[q]? = some Native.deltaKeys[q] := Array.getElem?_eq_getElem hq
      have e2 : Native.deltaKeys[q]! = Native.deltaKeys[q] := getElem!_pos Native.deltaKeys q hq
      rw [e1, Option.map_some]
      rw [deltaKeys_size] at hq
      simp [Native.cRows, Array.getElem?_ofFn, show 2 * q < 248 by omega, e2]
    · have e1 : Native.deltaKeys[q]? = none := Array.getElem?_eq_none (by omega)
      rw [e1, Option.map_none]
      rw [deltaKeys_size] at hq
      simp [Native.cRows, Array.getElem?_ofFn, show ¬ 2 * q < 248 by omega]
  · rw [getElem?_keyRows_two_mul_add_one, Array.getElem?_toList]
    by_cases hq : q < Native.deltaKeys.size
    · have e1 : Native.deltaKeys[q]? = some Native.deltaKeys[q] := Array.getElem?_eq_getElem hq
      have e2 : Native.deltaKeys[q]! = Native.deltaKeys[q] := getElem!_pos Native.deltaKeys q hq
      rw [e1, Option.map_some]
      rw [deltaKeys_size] at hq
      simp [Native.cRows, Array.getElem?_ofFn, show 2 * q + 1 < 248 by omega,
        show (2 * q + 1) / 2 = q by omega, e2]
    · have e1 : Native.deltaKeys[q]? = none := Array.getElem?_eq_none (by omega)
      rw [e1, Option.map_none]
      rw [deltaKeys_size] at hq
      simp [Native.cRows, Array.getElem?_ofFn, show ¬ 2 * q + 1 < 248 by omega]

theorem wfRows_cRows : WfRows (Native.cRows ()) := by
  rw [cRows_eq_deltaRows]
  refine ⟨by decide +kernel, fun x hx => ?_⟩
  have h : BaseS.deltaRows.all Native.V4.wf = true := by decide +kernel
  exact List.all_eq_true.1 h x (List.mem_toArray.1 hx)

theorem mul_mul_transpose_apply (A B : Matrix (Fin 248) (Fin 248) (ZMod 2)) (r s : Fin 248) :
    (A * B * A.transpose) r s = (fun k => A r k) ⬝ᵥ (B *ᵥ fun k => A s k) := by
  rw [Matrix.mul_assoc]
  rfl

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE F C G : Nat}

theorem pkMat_gram (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hF : SeedS.packOK F SeedS.fcRowsList = true) (hC : SeedS.packOK C BaseS.deltaRows = true)
    (hG : Nat.beq (mulB c rm (mulB c rm C F) (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 C)) G = true) :
    pkMat G = rowsMatrix BaseS.deltaRows.toArray * formF *
      (rowsMatrix BaseS.deltaRows.toArray).transpose := by
  rw [← Nat.eq_of_beq_eq_true hG, pkMat_mulB hk, pkMat_mulB hk, pkMat_trB hk, packOK_sound hC,
    packOK_sound hF, fcRowsList_toArray]

theorem pkMat_gram_apply (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hF : SeedS.packOK F SeedS.fcRowsList = true) (hC : SeedS.packOK C BaseS.deltaRows = true)
    (hG : Nat.beq (mulB c rm (mulB c rm C F) (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 C)) G = true)
    {i j : Nat} (hi : i < 124) (hj : j < 124) (a b : Fin 2) :
    pkMat G ⟨2 * i + a.val, by omega⟩ ⟨2 * j + b.val, by omega⟩ =
      keyVec (Native.deltaKeys[i]!) a ⬝ᵥ (formF *ᵥ keyVec (Native.deltaKeys[j]!) b) := by
  have hr : (fun k => rowsMatrix BaseS.deltaRows.toArray ⟨2 * i + a.val, by omega⟩ k) =
      keyVec (Native.deltaKeys[i]!) a := funext fun k => rowsMatrix_deltaRows_apply hi a k
  have hs : (fun k => rowsMatrix BaseS.deltaRows.toArray ⟨2 * j + b.val, by omega⟩ k) =
      keyVec (Native.deltaKeys[j]!) b := funext fun k => rowsMatrix_deltaRows_apply hj b k
  rw [pkMat_gram hk hF hC hG, mul_mul_transpose_apply, hr, hs]

theorem bit_eq (x k : Nat) : CFSG.KC.Th.bit x k = if x.testBit k then 1 else 0 := by
  change (x >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [h]

theorem bit_rowB (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true) (G : Nat)
    (r j : Fin 248) : CFSG.KC.Th.bit (rowB rm G r.val) j.val = (pkMat G r j).val := by
  have h := congrFun (pkVec_rowB hk G r) j
  rw [pkVec_apply] at h
  rw [bit_eq]
  by_cases hb : (rowB rm G r.val).testBit j.val = true
  · rw [if_pos hb] at h
    rw [if_pos hb, ← h]
    rfl
  · rw [if_neg hb] at h
    rw [if_neg hb, ← h]
    rfl

theorem blkG_eq_gramCode (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (G : Nat) {i j : Nat} (hi : i < 124) (hj : j < 124) :
    blkG rm G i j = gramCode fun a b =>
      pkMat G ⟨2 * i + a.val, by omega⟩ ⟨2 * j + b.val, by omega⟩ := by
  have e00 := bit_rowB hk G ⟨2 * i, by omega⟩ ⟨2 * j, by omega⟩
  have e01 := bit_rowB hk G ⟨2 * i, by omega⟩ ⟨2 * j + 1, by omega⟩
  have e10 := bit_rowB hk G ⟨2 * i + 1, by omega⟩ ⟨2 * j, by omega⟩
  have e11 := bit_rowB hk G ⟨2 * i + 1, by omega⟩ ⟨2 * j + 1, by omega⟩
  unfold blkG blk gramCode
  simp only [Nat.mul_eq, Nat.add_eq, Nat.succ_eq_add_one] at e00 e01 e10 e11 ⊢
  rw [e00, e01, e10, e11]
  exact (Nat.add_assoc _ _ _).symm

theorem blkG_eq_baseCode (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hF : SeedS.packOK F SeedS.fcRowsList = true) (hC : SeedS.packOK C BaseS.deltaRows = true)
    (hG : Nat.beq (mulB c rm (mulB c rm C F) (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 C)) G = true)
    {i j : Nat} (hi : i < 124) (hj : j < 124) : blkG rm G i j = Native.baseCode i j := by
  rw [blkG_eq_gramCode hk G hi hj, Native.baseCode, gramCodeN_formT]
  exact congrArg gramCode
    (funext fun a => funext fun b => pkMat_gram_apply hk hF hC hG hi hj a b)

theorem formBaseCheck_baseCode
    (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hF : SeedS.packOK F SeedS.fcRowsList = true) (hC : SeedS.packOK C BaseS.deltaRows = true)
    (hG : Nat.beq (mulB c rm (mulB c rm C F) (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 C)) G = true)
    (hB : formBaseCheck 124 (blkG rm G) = true) : formBaseCheck 124 Native.baseCode = true :=
  (formBaseCheck_congr fun _ _ hi hj => (blkG_eq_baseCode hk hF hC hG hi hj).symm).trans hB

end Consts

end CFSG.KC.Th.Spec

end
