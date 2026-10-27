module

public import Certificates.Data.Kernel.L5.Sh2Chk
public import CFSG.GH74.GLS.C3.Layer2.L5C5g
public import CFSG.Certificates.Kernel.L5.Tables

public section

namespace CFSG.Certificates.Kernel.L5Sh2

open Equiv Perm CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD.L5 CFSG.KD

theorem getD_flatMap_uniform {α β : Type*} (L : List α) (f : α → List β) (k : Nat)
    (hk : ∀ a, (f a).length = k) {i j : Nat} (hi : i < L.length) (hj : j < k) (d : β)
    (da : α) : (L.flatMap f).getD (i * k + j) d = (f (L.getD i da)).getD j d := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a L ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hk]; exact hj)]
      rfl
    | succ i =>
      have e : (i + 1) * k + j = (f a).length + (i * k + j) := by
        rw [hk, Nat.succ_mul]
        omega
      rw [e, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
        ih (by simp at hi; omega)]
      rfl

theorem Sh0L_getD {i : Nat} (hi : i < 128) :
    Sh0L.getD i 1 = tr16 ⟨i / 8, by omega⟩ * d8L.getD (i % 8) 1 := by
  have e : i = i / 8 * 8 + i % 8 := by omega
  have h := getD_flatMap_uniform (List.finRange 16) (fun v => d8L.map fun d => tr16 v * d) 8
    (fun a => by simp [d8L]) (i := i / 8) (j := i % 8) (by simp; omega) (by omega) 1 0
  rw [← e] at h
  have hv : (List.finRange 16).getD (i / 8) 0 = ⟨i / 8, by omega⟩ := by
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp
  unfold Sh0L
  rw [h, hv, List.getD_eq_getElem _ _ (by simp [d8L]; omega), List.getElem_map,
    List.getD_eq_getElem d8L _ (by simp [d8L]; omega)]

theorem act_lt (d x : Nat) : actN d x < 16 := Nat.mod_lt _ (by norm_num)

theorem xor_lt16 {x y : Nat} (hx : x < 16) (hy : y < 16) : x ^^^ y < 16 :=
  Nat.xor_lt_two_pow (n := 4) hx hy

theorem xor_cancel3 (A B v : Nat) : (A ^^^ B ^^^ v) ^^^ (B ^^^ v) = A := by
  rw [Nat.xor_assoc A B v, Nat.xor_assoc A (B ^^^ v) (B ^^^ v), Nat.xor_self, Nat.xor_zero]

theorem grp_mul_eq_of {M : Type} [Group M] (D : TabData M) (f : Idx D.n → Idx D.n → Idx D.n)
    (hf : ∀ a b, (f a b).v = D.tab.getD (a.v * D.n + b.v) 0) : ∀ a b, f a b = D.grp.mul a b :=
  fun a b => Idx.ext (by rw [hf]; rfl)

theorem oneI_eq
    (ty : Fin 4) : oneI = (sh2TabD ty).grp.one :=
  rfl

section Checks

variable (hc : sh2MulChk = true)
include hc

theorem actChk_of : actChk = true := by
  simp only [sh2MulChk, Bool.and_eq_true] at hc
  exact hc.1.1.1

theorem natChk_of : natChk = true := by
  simp only [sh2MulChk, Bool.and_eq_true] at hc
  exact hc.1.1.2

theorem gamTChk_of : gamTChk = true := by
  simp only [sh2MulChk, Bool.and_eq_true] at hc
  exact hc.1.2

theorem invChk_of : invChk = true := by
  simp only [sh2MulChk, Bool.and_eq_true] at hc
  exact hc.2

theorem d8_apply {d : Nat} (hd : d < 8) (w : Fin 16) : ((d8L.getD d 1) w).val = actN d w.val := by
  have h := actChk_of hc
  simp only [actChk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h d hd).1 w (List.mem_finRange w)

theorem d8_idxOf {d : Nat} (hd : d < 8) : d8L.idxOf (d8L.getD d 1) = d := by
  have h := actChk_of hc
  simp only [actChk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h d hd).2

theorem act_xor {d x y : Nat} (hd : d < 8) (hx : x < 16) (hy : y < 16) :
    actN d (x ^^^ y) = actN d x ^^^ actN d y := by
  have h := natChk_of hc
  simp only [natChk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h d hd).1 x hx y hy

theorem m8_lt {d e : Nat} (hd : d < 8) (he : e < 8) : m8N d e < 8 := by
  have h := natChk_of hc
  simp only [natChk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ((h d hd).2 e he).1

theorem act_act {d e x : Nat} (hd : d < 8) (he : e < 8) (hx : x < 16) :
    actN d (actN e x) = actN (m8N d e) x := by
  have h := natChk_of hc
  simp only [natChk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ((h d hd).2 e he).2 x hx

theorem act_zero {d : Nat} (hd : d < 8) : actN d 0 = 0 := by
  have h := act_xor hc hd (x := 0) (y := 0) (by norm_num) (by norm_num)
  rw [Nat.xor_self, Nat.xor_self] at h
  exact h

theorem idx0_mul {i j : Nat} (hi : i < 128) (hj : j < 128) :
    idx0 (Sh0L.getD i 1 * Sh0L.getD j 1) = m0N i j := by
  have hd : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have he : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hw : j / 8 < 16 := by omega
  have hv : i / 8 < 16 := by omega
  rw [Sh0L_getD hi, Sh0L_getD hj]
  set P := tr16 ⟨i / 8, hv⟩ * d8L.getD (i % 8) 1 * (tr16 ⟨j / 8, hw⟩ * d8L.getD (j % 8) 1)
    with hP
  have hPx : ∀ x : Fin 16, (P x).val =
      (actN (i % 8) (actN (j % 8) x.val) ^^^ actN (i % 8) (j / 8)) ^^^ i / 8 := by
    intro x
    rw [hP]
    simp only [Perm.mul_apply, tr16, Equiv.coe_fn_mk, xor16, Fin.val_mk, d8_apply hc hd,
      d8_apply hc he]
    rw [act_xor hc hd (act_lt _ _) hw]
  have hP0 : (P 0).val = actN (i % 8) (j / 8) ^^^ i / 8 := by
    rw [hPx, Fin.val_zero, act_zero hc he, act_zero hc hd, Nat.zero_xor]
  have hT : tr16 (P 0) * P = d8L.getD (m8N (i % 8) (j % 8)) 1 := by
    ext x
    rw [Perm.mul_apply]
    simp only [tr16, Equiv.coe_fn_mk, xor16, Fin.val_mk]
    rw [d8_apply hc (m8_lt hc hd he), hPx, hP0, ← act_act hc hd he x.isLt, xor_cancel3]
  unfold idx0
  rw [hT, d8_idxOf hc (m8_lt hc hd he), hP0, m0N, Nat.xor_comm]

theorem mt0_eq {i j : Nat}
    (hi : i < 128) (hj : j < 128) : mt0.getD (i * 128 + j) 0 = m0N i j := by
  have h1 := idx0_dec0 (mt0_lt hi hj)
  rw [dec0_mul hi hj, Subgroup.coe_mul, dec0_val, dec0_val, idx0_mul hc hi hj] at h1
  exact h1.symm

theorem m0N_lt {i j : Nat} (hi : i < 128) (hj : j < 128) : m0N i j < 128 := by
  have hd : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have he : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h1 := xor_lt16 (x := i / 8) (y := actN (i % 8) (j / 8)) (by omega) (act_lt _ _)
  have h2 := m8_lt hc hd he
  unfold m0N
  omega

theorem mulS_eq :
    (fun a b => mt0.getD (a * 128 + b) 0) = mulS := by
  funext a b
  unfold mulS
  split_ifs with h
  · exact mt0_eq hc h.1 h.2
  · rfl

end Checks

theorem bfsWordsGo_eq (gs : List Nat) (fuel : Nat) (W : Array (Option (List Nat))) (fr : List Nat) :
    bfsWordsGo gs fuel W fr = bfsWordsGoT (fun a b => mt0.getD (a * 128 + b) 0) gs fuel W fr := by
  induction fuel generalizing W fr with
  | zero => rfl
  | succ f ih =>
    rw [bfsWordsGo, bfsWordsGoT]
    exact ih _ _

theorem evFrom_eq (x : List Nat) (a : Nat) (w : List Nat) :
    evFrom x a w = evFromT (fun a b => mt0.getD (a * 128 + b) 0) x a w := rfl

section Checks2

variable (hc : sh2MulChk = true)
include hc

theorem Wd_eq : Wd = WdT := by
  unfold Wd WdT
  rw [bfsWordsGo_eq, mulS_eq hc]

theorem gamTab_eq {m j : Nat}
    (hm : m < 4) (hj : j < 128) : (gamTabs.getD m #[]).getD j 0 = gamN m j := by
  have h := gamTChk_of hc
  simp only [gamTChk, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have hx : m < xsData.length := by simp [xsData]; omega
  have h1 : gamTabs.getD m #[] = gamArr (xsData.getD m []) := by
    unfold gamTabs
    rw [KT.getD_toArray, List.getD_eq_getElem (xsData.map gamArr) _ (by simpa using hx),
      List.getElem_map, List.getD_eq_getElem xsData _ hx]
  have h2 : (gamArr (xsData.getD m [])).getD j 0 = evI (xsData.getD m []) (Wd.getD j []) := by
    unfold gamArr
    rw [KT.getD_toArray, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getElem_range]
  rw [h1, h2, evI, evFrom_eq, mulS_eq hc, Wd_eq hc]
  exact h m hm j hj

theorem mulN_eq
    (ty : Fin 4) {a b : Nat} (ha : a < 256) (hb : b < 256) :
    mulN ty.val a b = (sh2Tab ty).getD (a * 256 + b) 0 := by
  rw [sh2Tab_get ty ha hb]
  have hi : a / 2 < 128 := by omega
  have hj : b / 2 < 128 := by omega
  have hg : gamN ty.val (b / 2) < 128 := by
    rw [← gamTab_eq hc ty.isLt hj]
    exact gamTab_lt hj
  have hs : ssData.getD ty.val 0 = ssN ty.val := rfl
  have hs' : ssN ty.val < 128 := by
    rw [← hs]
    exact (gam_facts ty.isLt).1
  rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2 <;>
    simp only [mulN, mul2, pdec2, pcode2, ha2, hb2, decide_true, decide_false,
      Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false, Bool.toNat_true, Bool.toNat_false,
      Nat.add_zero]
  · rw [mt0_eq hc hi hj]
  · rw [mt0_eq hc hi hj]
  · rw [gamTab_eq hc ty.isLt hj, mt0_eq hc hi hg]
  · rw [gamTab_eq hc ty.isLt hj, mt0_eq hc hi hg, hs, mt0_eq hc (m0N_lt hc hi hg) hs']

theorem mulN_eqD
    (ty : Fin 4) {a b : Nat} (ha : a < 256) (hb : b < 256) :
    mulN ty.val a b = (sh2TabD ty).tab.getD (a * (sh2TabD ty).n + b) 0 := by
  have ht : (sh2TabD ty).tab = sh2Tab ty := by dsimp only [sh2TabD]
  have hn : (sh2TabD ty).n = 256 := by dsimp only [sh2TabD]
  rw [ht, hn]
  exact mulN_eq hc ty ha hb

theorem mulI_eq'
    (ty : Fin 4) :
    ∀ a b : Idx 256, mulI ty.val a b = (sh2TabD ty).grp.mul a b := by
  refine grp_mul_eq_of (sh2TabD ty) (mulI ty.val) fun a b => ?_
  show mulN ty.val a.v b.v % 256 = _
  rw [mulN_eqD hc ty (Idx.v_lt a) (Idx.v_lt b)]
  exact Nat.mod_eq_of_lt ((sh2TabD ty).lt_tab a b)

theorem invI_eq
    (ty : Fin 4) :
    ∀ a : Idx 256, invI ty.val a = (sh2TabD ty).grp.inv a := by
  letI G : Group (Idx 256) := (sh2TabD ty).grp
  intro a
  have h := invChk_of hc
  simp only [invChk, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have e2 : (mulI ty.val a (invI ty.val a)).v = mulN ty.val a.v (invN ty.val a.v) % 256 := rfl
  have h4 : mulI ty.val a (invI ty.val a) = oneI := by
    apply Idx.ext
    rw [e2, h ty.val ty.isLt a.v (Idx.v_lt a)]
    rfl
  have h1 : a * invI ty.val a = 1 := by
    rw [oneI_eq ty, mulI_eq' hc ty] at h4
    exact h4
  exact eq_inv_of_mul_eq_one_right h1

end Checks2

end CFSG.Certificates.Kernel.L5Sh2

end
