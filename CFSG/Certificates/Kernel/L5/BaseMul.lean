module

public import Certificates.Data.Kernel.L5.BaseMul

public section

namespace CFSG.KD.L5

open Equiv CFSG.GH74.GLS.C3.Layer2.L5.Fus

theorem foldl16_eq (L : List Nat) : ∀ a : Nat,
    L.foldl (fun acc x => acc * 16 + x) a =
      a * 16 ^ L.length + L.foldl (fun acc x => acc * 16 + x) 0 := by
  induction L with
  | nil => intro a; simp
  | cons x L ih =>
    intro a
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (a * 16 + x), ih (0 * 16 + x), pow_succ]
    ring

theorem foldl16_lt (L : List Nat) (hL : ∀ x ∈ L, x < 16) :
    L.foldl (fun acc x => acc * 16 + x) 0 < 16 ^ L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl16_eq L (0 * 16 + x), pow_succ]
    have hx : x < 16 := hL x (List.mem_cons_self ..)
    have hR := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    have : (x + 1) * 16 ^ L.length ≤ 16 ^ L.length * 16 := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ hx
    nlinarith

theorem foldl16_digit (L : List Nat) (hL : ∀ x ∈ L, x < 16) :
    ∀ i (hi : i < L.length),
      (L.foldl (fun acc x => acc * 16 + x) 0 / 16 ^ (L.length - 1 - i)) % 16 = L[i] := by
  induction L with
  | nil => intro i hi; simp at hi
  | cons x L ih =>
    intro i hi
    have hx : x < 16 := hL x (List.mem_cons_self ..)
    have hL' : ∀ y ∈ L, y < 16 := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    have hR := foldl16_lt L hL'
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl16_eq L (0 * 16 + x)]
    set R := L.foldl (fun acc x => acc * 16 + x) 0
    have hpos : 0 < 16 ^ L.length := Nat.pow_pos (by norm_num)
    cases i with
    | zero =>
      have e : L.length + 1 - 1 - 0 = L.length := by omega
      rw [e, Nat.zero_mul, Nat.zero_add, Nat.add_comm, Nat.add_mul_div_right _ _ hpos,
        Nat.div_eq_of_lt hR, Nat.zero_add, Nat.mod_eq_of_lt hx]
      rfl
    | succ j =>
      have hj : j < L.length := by simp at hi; omega
      set m := L.length - 1 - j with hm
      have e : L.length + 1 - 1 - (j + 1) = m := by omega
      have hk : L.length = m + (L.length - m) := by omega
      have hpm : 0 < 16 ^ m := Nat.pow_pos (by norm_num)
      have hsplit : (0 * 16 + x) * 16 ^ L.length =
          16 * (x * 16 ^ (L.length - m - 1)) * 16 ^ m := by
        have e2 : L.length = m + (L.length - m - 1) + 1 := by omega
        rw [e2, pow_succ, pow_add]
        have e3 : m + (L.length - m - 1) + 1 - m - 1 = L.length - m - 1 := by omega
        rw [e3]
        ring
      rw [e, hsplit, Nat.add_comm, Nat.add_mul_div_right _ _ hpm, Nat.add_mul_mod_self_left]
      rw [List.getElem_cons_succ, ← ih hL' j hj]

theorem codeP16_foldl (p : Perm (Fin 16)) : codeP16 p =
    ((List.finRange 16).map fun i => (p i).val).foldl (fun acc x => acc * 16 + x) 0 := by
  rw [codeP16, List.foldl_map]

theorem dg_codeP16 (p : Perm (Fin 16)) (i : Fin 16) : dg (codeP16 p) i.val = (p i).val := by
  have hL : ∀ x ∈ (List.finRange 16).map (fun i => (p i).val), x < 16 := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact (p j).isLt
  have h := foldl16_digit _ hL i.val (by simp)
  rw [← codeP16_foldl] at h
  simp only [List.length_map, List.length_finRange, List.getElem_map, List.getElem_finRange] at h
  have e : 16 - 1 - i.val = 15 - i.val := by omega
  rw [e] at h
  unfold dg
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  exact h

theorem mulB_v (n C K kw b0 b1 : Nat) (a b : Idx n) :
    (mulB n C K kw b0 b1 a b).v = mulBN n C K kw b0 b1 a.v b.v := rfl

theorem mulB_eq {M : Type} [Group M] (D : TabData M) (f : M →* Perm (Fin 16))
    {C K kw b0 b1 : Nat} (hb0 : b0 < 16) (hb1 : b1 < 16)
    (hC : ∀ a : Idx D.n, codeP16 (f (D.e a)) = cget C 64 a.v)
    (hK : ∀ a : Idx D.n, keyN K kw (dg (cget C 64 a.v) b0) (dg (cget C 64 a.v) b1) = a.v) :
    ∀ a b : Idx D.n, mulB D.n C K kw b0 b1 a b = D.grp.mul a b := by
  intro a b
  apply Idx.ext
  have hc : D.e (D.mulI a b) = D.e a * D.e b := D.e_mulI a b
  have hdig : ∀ (i : Nat) (hi : i < 16),
      dg (cget C 64 a.v) (dg (cget C 64 b.v) i) = dg (cget C 64 (D.mulI a b).v) i := by
    intro i hi
    have h1 : dg (cget C 64 b.v) i = (f (D.e b) ⟨i, hi⟩).val := by
      rw [← hC b]
      exact dg_codeP16 _ ⟨i, hi⟩
    rw [h1, ← hC a, dg_codeP16, ← hC (D.mulI a b), dg_codeP16 _ ⟨i, hi⟩, hc, map_mul,
      Perm.mul_apply]
  rw [mulB_v]
  unfold mulBN
  simp only
  rw [hdig b0 hb0, hdig b1 hb1, hK (D.mulI a b), Nat.mod_eq_of_lt (Idx.v_lt _)]
  rfl

theorem mkTabData_e {M : Type} [Group M] [DecidableEq M] (elems : List M) (code : M → Nat)
    (hc : ∀ m : M, m ∈ elems) (tab invT : Array Nat) (oneI : Nat)
    (hchk : tabCheck elems code tab invT oneI = true)
    (a : Idx (mkTabData elems code hc tab invT oneI hchk).n) :
    (mkTabData elems code hc tab invT oneI hchk).e a = elems.getD a.v 1 := by
  change elems.get a.i = _
  rw [Idx.v, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h := a.i.isLt),
    Option.getD_some]
  rfl

theorem codes_of {M : Type} [Group M] {f : M → Perm (Fin 16)} {elems : List M} {C : Nat}
    (h : codesChk f elems C = true) {a : Nat} (ha : a < elems.length) :
    codeP16 (f (elems.getD a 1)) = cget C 64 a := by
  simp only [codesChk, decide_eq_true_eq] at h
  have h2 := congrArg (fun L => L[a]?) h
  simp only [List.getElem?_map, List.getElem?_range ha, List.getElem?_eq_getElem ha,
    Option.map_some, Option.some.injEq] at h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
  exact h2

theorem key_of {n C K kw b0 b1 : Nat} (h : keyChk n C K kw b0 b1 = true) (a : Idx n) :
    keyN K kw (dg (cget C 64 a.v) b0) (dg (cget C 64 a.v) b1) = a.v := by
  simp only [keyChk, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h a.v a.v_lt

theorem invB_eq {n C K kw b0 b1 I o : Nat} (G : Group (Idx n))
    (hm : ∀ a b, mulB n C K kw b0 b1 a b = G.mul a b) (ho : G.one.v = o)
    (h : invChkB n C K kw b0 b1 I o = true) : ∀ a, invB n I kw a = G.inv a := by
  let _ : Group (Idx n) := G
  intro a
  simp only [invChkB,List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have h1 : a * invB n I kw a = 1 := by
    have h2 : mulB n C K kw b0 b1 a (invB n I kw a) = G.one := Idx.ext (by
      rw [mulB_v, ho]
      exact h a.v a.v_lt)
    rw [hm] at h2
    exact h2
  exact eq_inv_of_mul_eq_one_right h1

end CFSG.KD.L5

end
