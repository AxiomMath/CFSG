module

public import Certificates.Data.Kernel.LyFive.G2
public import CFSG.Certificates.Kernel.LyFive.G2Theory
public import CFSG.Certificates.Kernel.SporSch.LySevCbfs
import CFSG.Certificates.Kernel.SporSch.LyLoop
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.LyMatSound

public section

namespace CFSG.KS.LyFive.G2

open CFSG.KC.LyG2 CFSG.KC.Enum CFSG.KS.SporSch.LySev CFSG.KS.SporSch.LySvC CFSG.KS.SporSch.LyLoop
open Matrix

@[expose] noncomputable def dv (x : ℕ) : V := fun i => ((ln x i.val : ℕ) : ZMod 5)

@[expose] def Can (x : ℕ) : Prop := x < 2 ^ 140 ∧ ∀ i < 7, ln x i < 5

theorem ln_eq (x i : ℕ) : ln x i = x / 2 ^ (20 * i) % 2 ^ 20 := fldK_eq x (20 * i)

theorem can_repr {x : ℕ} (h : Can x) : x = laneSum (fun L => ln x L) 7 := by
  have := lane_repr (n := 7) (X := x) (by simpa using h.1)
  simpa [ln_eq] using this

theorem ln_laneSum {v : ℕ → ℕ} (hv : ∀ L < 7, v L < 2 ^ 20) {i : ℕ} (hi : i < 7) :
    ln (laneSum v 7) i = v i := by
  rw [ln_eq]
  exact lane_get hv i hi

theorem can_laneSum {v : ℕ → ℕ} (hv : ∀ L < 7, v L < 5) : Can (laneSum v 7) := by
  have hv' : ∀ L < 7, v L < 2 ^ 20 := fun L hL => by have := hv L hL; omega
  refine ⟨by simpa using lane_lt hv', fun i hi => ?_⟩
  rw [ln_laneSum hv' hi]
  exact hv i hi

theorem dv_laneSum {v : ℕ → ℕ} (hv : ∀ L < 7, v L < 2 ^ 20) (i : Fin 7) :
    dv (laneSum v 7) i = (v i : ZMod 5) := by
  rw [dv, ln_laneSum hv i.isLt]

theorem can_zero : Can 0 := ⟨by norm_num, fun i _ => by rw [ln_eq]; simp⟩

theorem dv_zero : dv 0 = 0 := by
  funext i
  simp [dv, ln_eq]

theorem can_eq {x y : ℕ} (hx : Can x) (hy : Can y) (h : dv x = dv y) : x = y := by
  rw [can_repr hx, can_repr hy]
  unfold laneSum
  refine Finset.sum_congr rfl fun L hL => ?_
  have hL' := Finset.mem_range.1 hL
  have e := congrFun h ⟨L, hL'⟩
  simp only [dv] at e
  have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
  rw [Nat.mod_eq_of_lt (hx.2 L hL'), Nat.mod_eq_of_lt (hy.2 L hL')] at this
  change ln x L * 2 ^ (20 * L) = ln y L * 2 ^ (20 * L)
  rw [this]

theorem QM7_beq : Nat.beq QM7 (qmB 7) = true := by quickRfl

theorem QM7_eq : QM7 = qmB 7 := Nat.eq_of_beq_eq_true QM7_beq

theorem red5_lanes {u : ℕ → ℕ} (hu : ∀ L < 7, u L < 1024) :
    red5 QM7 (laneSum u 7) = laneSum (fun L => u L % 5) 7 := by
  rw [QM7_eq]
  exact red5_eq hu

theorem getL_nil (i : ℕ) : getL [] i = 0 := rfl

theorem getL_cons_succ (a : ℕ) (l : List ℕ) (i : ℕ) : getL (a :: l) (i + 1) = getL l i := rfl

theorem getL_eq : ∀ (l : List ℕ) (i : ℕ), getL l i = l.getD i 0
  | [], i => by simp [getL_nil]
  | a :: l, 0 => rfl
  | a :: l, i + 1 => by rw [getL_cons_succ, getL_eq l i]; rfl

theorem getLL_eq : ∀ (l : List (List ℕ)) (i : ℕ), getLL l i = l.getD i []
  | [], i => by cases i <;> rfl
  | a :: l, 0 => rfl
  | a :: l, i + 1 => by
    change getLL l i = (a :: l).getD (i + 1) []
    rw [getLL_eq l i]
    rfl

theorem snoc_eq (l : List ℕ) (x : ℕ) : snoc l x = l ++ [x] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change a :: snoc l x = _
    rw [ih]
    rfl

theorem can_snoc {l : List ℕ} {v : ℕ} (hl : ∀ x ∈ l, Can x) (hv : Can v) : ∀ x ∈ snoc l v, Can x := by
  intro x hx
  rw [snoc_eq, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx
  · exact hl x hx
  · rw [hx]
    exact hv

theorem lenL_eq (l : List ℕ) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Nat.succ (lenL l) = _
    rw [ih]
    rfl

theorem redL_iff (l : List ℕ) : redL l = true ↔ ∀ x ∈ l, Can x := by
  induction l with
  | nil => simp [redL]
  | cons v l ih =>
    change bAnd(Nat.blt v 1393796574908163946345982392040522594123776,
      bAnd(Nat.blt (ln v 0) 5, bAnd(Nat.blt (ln v 1) 5, bAnd(Nat.blt (ln v 2) 5,
      bAnd(Nat.blt (ln v 3) 5, bAnd(Nat.blt (ln v 4) 5, bAnd(Nat.blt (ln v 5) 5,
      bAnd(Nat.blt (ln v 6) 5, redL l)))))))) = true ↔ _
    have e140 : (2 : ℕ) ^ 140 = 1393796574908163946345982392040522594123776 := by norm_num
    simp only [bAnd_eqP, Bool.and_eq_true, Nat.blt_eq, ih, List.forall_mem_cons]
    constructor
    · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
      refine ⟨⟨by rw [e140]; exact h0, fun i hi => ?_⟩, h8⟩
      match i, hi with
      | 0, _ => exact h1
      | 1, _ => exact h2
      | 2, _ => exact h3
      | 3, _ => exact h4
      | 4, _ => exact h5
      | 5, _ => exact h6
      | 6, _ => exact h7
      | n + 7, h => exact absurd h (by omega)
    · rintro ⟨⟨h0, hl⟩, h8⟩
      exact ⟨by rw [← e140]; exact h0, hl 0 (by omega), hl 1 (by omega), hl 2 (by omega),
        hl 3 (by omega), hl 4 (by omega), hl 5 (by omega), hl 6 (by omega), h8⟩

theorem can_getL {l : List ℕ} (h : ∀ x ∈ l, Can x) (i : ℕ) : Can (getL l i) := by
  rw [getL_eq]
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact can_zero

theorem dv_getL (l : List ℕ) (i : ℕ) : dv (getL l i) = (l.map dv).getD i 0 := by
  rw [getL_eq, ← dv_zero, List.getD_map]

theorem sum_le_of {n B : ℕ} {f : ℕ → ℕ} (h : ∀ t < n, f t ≤ B) :
    ∑ t ∈ Finset.range n, f t ≤ n * B := by
  calc ∑ t ∈ Finset.range n, f t ≤ ∑ _t ∈ Finset.range n, B :=
        Finset.sum_le_sum fun t ht => h t (Finset.mem_range.1 ht)
    _ = n * B := by simp

theorem red5_comb {n : ℕ} (a w : ℕ → ℕ) (hw : ∀ t < n, Can (w t)) (hb : ∀ t < n, a t < 5)
    (hn : n ≤ 63) :
    Can (red5 QM7 (∑ t ∈ Finset.range n, a t * w t)) ∧
      dv (red5 QM7 (∑ t ∈ Finset.range n, a t * w t)) = ∑ t ∈ Finset.range n, (a t : ZMod 5) • dv (w t) := by
  have e : ∑ t ∈ Finset.range n, a t * w t =
      laneSum (fun L => ∑ t ∈ Finset.range n, a t * ln (w t) L) 7 := by
    rw [← laneSum_comb]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← can_repr (hw t (Finset.mem_range.1 ht))]
  have hbd : ∀ L < 7, ∑ t ∈ Finset.range n, a t * ln (w t) L < 1024 := by
    intro L hL
    have := sum_le_of (n := n) (B := 16) (f := fun t => a t * ln (w t) L) fun t ht => by
      have h1 := hb t ht
      have h2 := (hw t ht).2 L hL
      have : a t * ln (w t) L ≤ 4 * 4 := Nat.mul_le_mul (by omega) (by omega)
      omega
    omega
  rw [e, red5_lanes hbd]
  refine ⟨can_laneSum fun L _ => Nat.mod_lt _ (by norm_num), ?_⟩
  have hlt : ∀ L < 7, (∑ t ∈ Finset.range n, a t * ln (w t) L) % 5 < 2 ^ 20 := by
    intro L _
    have := Nat.mod_lt (∑ t ∈ Finset.range n, a t * ln (w t) L) (show 0 < 5 by norm_num)
    omega
  funext i
  rw [dv_laneSum hlt i, Finset.sum_apply]
  simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul, Pi.smul_apply, smul_eq_mul, dv]

@[expose] noncomputable def colM (cols : List ℕ) : M := Matrix.of fun r t => dv (getL cols t.val) r

theorem colSum_eq (v : ℕ) : ∀ (cs : List ℕ) (j : ℕ),
    colSum v cs j = ∑ t ∈ Finset.range cs.length, ln v (j + t) * getL cs t
  | [], j => rfl
  | c :: cs, j => by
    change ln v j * c + colSum v cs (j + 1) = _
    rw [colSum_eq v cs (j + 1), List.length_cons, Finset.sum_range_succ', add_comm]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun t _ => ?_) rfl
    rw [show j + 1 + t = j + (t + 1) by omega]
    rfl

theorem sum_range_seven {n : ℕ} (hn : n ≤ 7) (f : ℕ → V) (hf : ∀ t, n ≤ t → f t = 0) :
    ∑ t ∈ Finset.range n, f t = ∑ t : Fin 7, f t.val := by
  rw [show (∑ t : Fin 7, f t.val) = ∑ t ∈ Finset.range 7, f t from Fin.sum_univ_eq_sum_range f 7]
  rw [← Finset.sum_range_add_sum_Ico _ hn]
  rw [Finset.sum_eq_zero (s := Finset.Ico n 7) fun t ht => hf t (Finset.mem_Ico.1 ht).1, add_zero]

theorem mvL_spec {cols : List ℕ} (hc : ∀ x ∈ cols, Can x) (hl : cols.length ≤ 7) {v : ℕ}
    (hv : Can v) : Can (mvL cols v) ∧ dv (mvL cols v) = colM cols *ᵥ dv v := by
  have h := red5_comb (n := cols.length) (fun t => ln v t) (fun t => getL cols t)
    (fun t _ => can_getL hc t) (fun t ht => hv.2 t (by omega)) (by omega)
  have e : mvL cols v = red5 QM7 (∑ t ∈ Finset.range cols.length, ln v t * getL cols t) := by
    unfold mvL
    rw [colSum_eq]
    simp only [Nat.zero_add]
  rw [e]
  refine ⟨h.1, ?_⟩
  rw [h.2]
  have hz : ∀ t, cols.length ≤ t → ((ln v t : ℕ) : ZMod 5) • dv (getL cols t) = 0 := by
    intro t ht
    rw [getL_eq, List.getD_eq_default _ _ ht, dv_zero, smul_zero]
  rw [sum_range_seven hl _ hz]
  funext r
  rw [Finset.sum_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, colM, of_apply, dv]
  ring

@[expose] noncomputable def ccOf (CC : List (List ℕ)) : Fin 7 → Fin 7 → V :=
  fun i j => dv (getL (getLL CC i.val) j.val)

@[expose] def TabOK (CC : List (List ℕ)) : Prop := CC.length ≤ 7 ∧ ∀ row ∈ CC, row.length ≤ 7 ∧ ∀ x ∈ row, Can x

theorem crsSum_eq (CC : List (List ℕ)) (u v : ℕ) : ∀ (i : ℕ),
    crsSum CC u v i = ∑ t ∈ Finset.range CC.length, ln u (i + t) * mvL (getLL CC t) v := by
  induction CC with
  | nil => intro i; rfl
  | cons row CC ih =>
    intro i
    change ln u i * mvL row v + crsSum CC u v (i + 1) = _
    rw [ih (i + 1), List.length_cons, Finset.sum_range_succ', add_comm]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun t _ => ?_) rfl
    rw [show i + 1 + t = i + (t + 1) by omega]
    rfl

theorem colM_row_mulVec {CC : List (List ℕ)} (i : Fin 7) (v : V) :
    colM (getLL CC i.val) *ᵥ v = ∑ j : Fin 7, v j • ccOf CC i j := by
  funext r
  rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [colM, of_apply, ccOf, Pi.smul_apply, smul_eq_mul]
  ring

theorem crs_spec {CC : List (List ℕ)} (hCC : TabOK CC) {u v : ℕ} (hu : Can u) (hv : Can v) :
    Can (crs CC u v) ∧ dv (crs CC u v) = cr (ccOf CC) (dv u) (dv v) := by
  have hrow : ∀ t, (∀ x ∈ getLL CC t, Can x) ∧ (getLL CC t).length ≤ 7 := by
    intro t
    rw [getLL_eq]
    by_cases ht : t < CC.length
    · rw [List.getD_eq_getElem _ _ ht]
      have := hCC.2 _ (List.getElem_mem ht)
      exact ⟨this.2, this.1⟩
    · rw [List.getD_eq_default _ _ (by omega)]
      exact ⟨fun x hx => absurd hx (List.not_mem_nil), by simp⟩
  have hw : ∀ t, Can (mvL (getLL CC t) v) := fun t => (mvL_spec (hrow t).1 (hrow t).2 hv).1
  have h := red5_comb (n := CC.length) (fun t => ln u t) (fun t => mvL (getLL CC t) v)
    (fun t _ => hw t) (fun t ht => hu.2 t (by have := hCC.1; omega)) (by have := hCC.1; omega)
  have e : crs CC u v = red5 QM7 (∑ t ∈ Finset.range CC.length, ln u t * mvL (getLL CC t) v) := by
    unfold crs
    rw [crsSum_eq]
    simp only [Nat.zero_add]
  rw [e]
  refine ⟨h.1, ?_⟩
  rw [h.2]
  have hz : ∀ t, CC.length ≤ t → ((ln u t : ℕ) : ZMod 5) • dv (mvL (getLL CC t) v) = 0 := by
    intro t ht
    have : getLL CC t = [] := by rw [getLL_eq, List.getD_eq_default _ _ ht]
    rw [this]
    change _ • dv (red5 QM7 0) = 0
    rw [show red5 QM7 0 = 0 from Nat.zero_sub _, dv_zero, smul_zero]
  rw [sum_range_seven hCC.1 _ hz, cr_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(mvL_spec (hrow i).1 (hrow i).2 hv).2, colM_row_mulVec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  rfl

theorem lnList_eq (u : ℕ) :
    [ln u (nat_lit 0), ln u (nat_lit 1), ln u (nat_lit 2), ln u (nat_lit 3), ln u (nat_lit 4),
      ln u (nat_lit 5), ln u (nat_lit 6)] = (List.range 7).map (ln u) := rfl

theorem bt_spec {TT : List ℕ} (hT : ∀ x ∈ TT, Can x) (hl : TT.length ≤ 7) {u v : ℕ} (hu : Can u)
    (hv : Can v) : bt TT u v < 5 ∧ ((bt TT u v : ℕ) : ZMod 5) = dv u ⬝ᵥ (colM TT *ᵥ dv v) := by
  obtain ⟨hw, ew⟩ := mvL_spec hT hl hv
  refine ⟨Nat.mod_lt _ (by norm_num), ?_⟩
  have e : bt TT u v = (∑ t ∈ Finset.range 7, ln (mvL TT v) t * ln u t) % 5 := by
    unfold bt
    rw [colSum_eq, lnList_eq, List.length_map, List.length_range]
    congr 1
  rw [e, ZMod.natCast_mod, ← ew, Nat.cast_sum, dotProduct,
    ← Fin.sum_univ_eq_sum_range (fun x => ((ln (mvL TT v) x * ln u x : ℕ) : ZMod 5)) 7]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.cast_mul, mul_comm]
  rfl

theorem linSum_eq : ∀ (cs us : List ℕ),
    linSum cs us = ∑ t ∈ Finset.range (min cs.length us.length), getL cs t * getL us t
  | [], us => by simp [linSum]
  | c :: cs, [] => by simp [linSum]
  | c :: cs, u :: us => by
    change c * u + linSum cs us = _
    rw [linSum_eq cs us, List.length_cons, List.length_cons, Nat.succ_min_succ,
      Finset.sum_range_succ', add_comm]
    rfl

theorem lc_eq : ∀ (cs : List ℕ) (us : List V),
    lc cs us = ∑ t ∈ Finset.range (min cs.length us.length), ((cs.getD t 0 : ℕ) : ZMod 5) • us.getD t 0
  | [], us => by simp [lc]
  | c :: cs, [] => by simp [lc]
  | c :: cs, u :: us => by
    have ih := lc_eq cs us
    simp only [lc, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, List.length_cons, List.length_cons, Nat.succ_min_succ, Finset.sum_range_succ', add_comm]
    rfl

theorem lin_spec {cs us : List ℕ} (hcs : cs.length ≤ 63) (hc : ∀ c ∈ cs, c < 5)
    (hus : ∀ x ∈ us, Can x) : Can (lin cs us) ∧ dv (lin cs us) = lc cs (us.map dv) := by
  have h := red5_comb (n := min cs.length us.length) (fun t => getL cs t) (fun t => getL us t)
    (fun t _ => can_getL hus t) (fun t ht => by
      rw [getL_eq, List.getD_eq_getElem _ _ (by omega)]
      exact hc _ (List.getElem_mem _)) (by omega)
  unfold lin
  rw [linSum_eq]
  refine ⟨h.1, ?_⟩
  rw [h.2, lc_eq, List.length_map]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dv_getL, getL_eq]

theorem beq_t {a b : ℕ} (h : a = b) : Nat.beq a b = true := by rw [h]; exact Nat.beq_refl b

theorem beq_f {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

structure DataOK (CC : List (List ℕ)) (TT : List ℕ) (ops : List (List ℕ)) : Prop where
  tab : TabOK CC
  tt : ∀ x ∈ TT, Can x
  ttLen : TT.length ≤ 7
  tβ : colM TT = Tβ (ccOf CC)
  ops : ∀ o ∈ ops, (∀ x ∈ o, Can x) ∧ o.length ≤ 7

theorem getLL_ops {ops : List (List ℕ)} (h : ∀ o ∈ ops, (∀ x ∈ o, Can x) ∧ o.length ≤ 7) (a : ℕ) :
    (∀ x ∈ getLL ops a, Can x) ∧ (getLL ops a).length ≤ 7 := by
  rw [getLL_eq]
  by_cases ha : a < ops.length
  · rw [List.getD_eq_getElem _ _ ha]
    exact h _ (List.getElem_mem ha)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨fun x hx => absurd hx (List.not_mem_nil), by simp⟩

theorem colM_nil : colM [] = 0 := by
  ext r t
  simp [colM, getL_nil, dv_zero]

theorem opsM_getD (ops : List (List ℕ)) (a : ℕ) : (ops.map colM).getD a 0 = colM (getLL ops a) := by
  rw [getLL_eq, ← colM_nil, List.getD_map]

theorem insOK_iff (ins : List (ℕ × ℕ × ℕ × List ℕ)) :
    insOK ins = true ↔ ∀ i ∈ ins, i.2.2.2.length ≤ 63 ∧ ∀ c ∈ i.2.2.2, c < 5 := by
  have hlt : ∀ l : List ℕ, lt5L l = true ↔ ∀ c ∈ l, c < 5 := by
    intro l
    induction l with
    | nil => simp [lt5L]
    | cons c l ih =>
      change bAnd(Nat.blt c 5, lt5L l) = true ↔ _
      rw [bAnd_eqP, Bool.and_eq_true, Nat.blt_eq, ih, List.forall_mem_cons]
  induction ins with
  | nil => simp [insOK]
  | cons i ins ih =>
    change bAnd(Nat.ble (lenL i.2.2.2) 63, bAnd(lt5L i.2.2.2, insOK ins)) = true ↔ _
    rw [bAnd_eqP, bAnd_eqP, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, lenL_eq, hlt]
    simp only [List.forall_mem_cons, ih]
    tauto

section Run

variable {CC : List (List ℕ)} {TT : List ℕ} {ops : List (List ℕ)} (hD : DataOK CC TT ops)
include hD

theorem bt_β {u v : ℕ} (hu : Can u) (hv : Can v) :
    bt TT u v < 5 ∧ ((bt TT u v : ℕ) : ZMod 5) = β (ccOf CC) (dv u) (dv v) := by
  obtain ⟨h1, h2⟩ := bt_spec hD.tt hD.ttLen hu hv
  rw [β_eq_dot, ← hD.tβ]
  exact ⟨h1, h2⟩

omit hD in
theorem bRec_eq {α : Sort _} (e t : α) (b : Bool) :
    Bool.rec (motive := fun _ => α) e t b = if b = true then t else e := by
  cases b <;> rfl

omit hD in
theorem stepI_eq (gv : List ℕ) (i : ℕ × ℕ × ℕ × List ℕ) (ih : List ℕ → Bool) (us : List ℕ) :
    stepI CC TT ops gv i ih us =
      if i.1 = 0 then ih (snoc us (getL gv i.2.1))
      else if i.1 = 1 then ih (snoc us (mvL (getLL ops i.2.1) (getL us i.2.2.1)))
      else if i.1 = 2 then ih (snoc us (crs CC (getL us i.2.1) (getL us i.2.2.1)))
      else if i.1 = 3 then
        (if mvL (getLL ops i.2.1) (getL us i.2.2.1) = lin i.2.2.2 us then ih us else false)
      else if i.1 = 4 then
        (if crs CC (getL us i.2.1) (getL us i.2.2.1) = lin i.2.2.2 us then ih us else false)
      else if i.1 = 5 then
        (if bt TT (getL us i.2.1) (getL us i.2.2.1) = getL i.2.2.2 0 then ih us else false)
      else if i.1 = 6 then (if (!Nat.beq (getL us i.2.1) 0) = true then ih us else false)
      else false := by
  unfold stepI
  simp only [bIf_eqP, bAnd_eqP, strictB_eqB, Nat.beq_eq]

omit hD in
theorem iteF {c : Prop} [Decidable c] {x : Bool} : ((if c then x else false) = true) ↔ c ∧ x = true := by
  by_cases h : c
  · rw [if_pos h]
    exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
  · rw [if_neg h]
    exact ⟨fun e => absurd e (by decide), fun e => absurd e.1 h⟩

omit hD in
theorem eq_iff_dv {x y : ℕ} (hx : Can x) (hy : Can y) : x = y ↔ dv x = dv y :=
  ⟨fun e => by rw [e], can_eq hx hy⟩

omit hD in
theorem stkI_cons (gv : List ℕ) (i : ℕ × ℕ × ℕ × List ℕ) (ins : List (ℕ × ℕ × ℕ × List ℕ))
    (us : List ℕ) : stkI CC ops gv (i :: ins) us =
      if i.1 = 0 then stkI CC ops gv ins (snoc us (getL gv i.2.1))
      else if i.1 = 1 then stkI CC ops gv ins (snoc us (mvL (getLL ops i.2.1) (getL us i.2.2.1)))
      else if i.1 = 2 then stkI CC ops gv ins (snoc us (crs CC (getL us i.2.1) (getL us i.2.2.1)))
      else stkI CC ops gv ins us := by
  change Bool.rec (motive := fun _ => List ℕ)
      (Bool.rec (motive := fun _ => List ℕ)
        (Bool.rec (motive := fun _ => List ℕ) (stkI CC ops gv ins us)
          (stkI CC ops gv ins (snoc us (crs CC (getL us i.2.1) (getL us i.2.2.1)))) (Nat.beq i.1 2))
        (stkI CC ops gv ins (snoc us (mvL (getLL ops i.2.1) (getL us i.2.2.1)))) (Nat.beq i.1 1))
      (stkI CC ops gv ins (snoc us (getL gv i.2.1))) (Nat.beq i.1 0) = _
  simp only [bRec_eq, Nat.beq_eq]

theorem runI_iff {gv : List ℕ} (hgv : ∀ x ∈ gv, Can x) :
    ∀ (ins : List (ℕ × ℕ × ℕ × List ℕ)), (∀ i ∈ ins, i.2.2.2.length ≤ 63 ∧ ∀ c ∈ i.2.2.2, c < 5) →
      ∀ (us : List ℕ), (∀ x ∈ us, Can x) →
        (runI CC TT ops gv ins us = true ↔
          mRun (ccOf CC) (ops.map colM) (gv.map dv) ins (us.map dv))
  | [], _, us, _ => by
    rw [mRun_nil]
    exact ⟨fun _ => trivial, fun _ => rfl⟩
  | i :: ins, hins, us, hus => by
    have hi := hins i List.mem_cons_self
    have hins' := fun j hj => hins j (List.mem_cons_of_mem _ hj)
    have ih := runI_iff hgv ins hins'
    have hpush : ∀ v, Can v → (∀ x ∈ snoc us v, Can x) := by
      intro v hv x hx
      rw [snoc_eq, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hus x hx
      · exact hv
    have hsnoc : ∀ v, (snoc us v).map dv = us.map dv ++ [dv v] := by
      intro v
      rw [snoc_eq, List.map_append, List.map_singleton]
    have hrun : runI CC TT ops gv (i :: ins) us = stepI CC TT ops gv i (runI CC TT ops gv ins) us :=
      rfl
    rw [hrun, stepI_eq, mRun_cons]
    unfold chkV pushV
    by_cases h0 : i.1 = 0
    · rw [if_pos h0, if_pos h0, if_pos h0, true_and]
      have hv := can_getL hgv i.2.1
      rw [ih _ (hpush _ hv), hsnoc, dv_getL]
    rw [if_neg h0, if_neg h0, if_neg h0]
    by_cases h1 : i.1 = 1
    · rw [if_pos h1, if_pos h1, if_pos h1, true_and]
      obtain ⟨ho1, ho2⟩ := getLL_ops hD.ops i.2.1
      obtain ⟨hv, ev⟩ := mvL_spec ho1 ho2 (can_getL hus i.2.2.1)
      rw [ih _ (hpush _ hv), hsnoc, ev, dv_getL, opsM_getD]
    rw [if_neg h1, if_neg h1, if_neg h1]
    by_cases h2 : i.1 = 2
    · rw [if_pos h2, if_pos h2, if_pos h2, true_and]
      obtain ⟨hv, ev⟩ := crs_spec hD.tab (can_getL hus i.2.1) (can_getL hus i.2.2.1)
      rw [ih _ (hpush _ hv), hsnoc, ev, dv_getL, dv_getL]
    rw [if_neg h2, if_neg h2, if_neg h2]
    by_cases h3 : i.1 = 3
    · rw [if_pos h3, if_pos h3, iteF, ih _ hus]
      obtain ⟨ho1, ho2⟩ := getLL_ops hD.ops i.2.1
      obtain ⟨hv, ev⟩ := mvL_spec ho1 ho2 (can_getL hus i.2.2.1)
      obtain ⟨hl, el⟩ := lin_spec hi.1 hi.2 hus
      rw [eq_iff_dv hv hl, ev, el, dv_getL, opsM_getD]
    rw [if_neg h3, if_neg h3]
    by_cases h4 : i.1 = 4
    · rw [if_pos h4, if_pos h4, iteF, ih _ hus]
      obtain ⟨hv, ev⟩ := crs_spec hD.tab (can_getL hus i.2.1) (can_getL hus i.2.2.1)
      obtain ⟨hl, el⟩ := lin_spec hi.1 hi.2 hus
      rw [eq_iff_dv hv hl, ev, el, dv_getL, dv_getL]
    rw [if_neg h4, if_neg h4]
    by_cases h5 : i.1 = 5
    · rw [if_pos h5, if_pos h5, iteF, ih _ hus]
      obtain ⟨hb1, hb2⟩ := bt_β hD (can_getL hus i.2.1) (can_getL hus i.2.2.1)
      have hc0 : getL i.2.2.2 0 < 5 := by
        rw [getL_eq]
        by_cases hn : 0 < i.2.2.2.length
        · rw [List.getD_eq_getElem _ _ hn]
          exact hi.2 _ (List.getElem_mem hn)
        · rw [List.getD_eq_default _ _ (by omega)]
          norm_num
      rw [← dv_getL, ← dv_getL, ← hb2, getL_eq i.2.2.2 0]
      rw [getL_eq] at hc0
      constructor
      · rintro ⟨e, h⟩
        exact ⟨by rw [e], h⟩
      · rintro ⟨e, h⟩
        refine ⟨?_, h⟩
        have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
        rwa [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hc0] at this
    rw [if_neg h5, if_neg h5]
    by_cases h6 : i.1 = 6
    · rw [if_pos h6, if_pos h6, iteF, ih _ hus, Bool.not_eq_true', ← dv_getL]
      have hv := can_getL hus i.2.1
      constructor
      · rintro ⟨e, h⟩
        refine ⟨fun e' => ?_, h⟩
        rw [← dv_zero] at e'
        rw [beq_t (can_eq hv can_zero e')] at e
        exact absurd e (by decide)
      · rintro ⟨e, h⟩
        refine ⟨beq_f fun e' => e (by rw [e', dv_zero]), h⟩
    rw [if_neg h6, if_neg h6]
    simp

theorem stkI_spec {gv : List ℕ} (hgv : ∀ x ∈ gv, Can x) :
    ∀ (ins : List (ℕ × ℕ × ℕ × List ℕ)) (us : List ℕ), (∀ x ∈ us, Can x) →
      (∀ x ∈ stkI CC ops gv ins us, Can x) ∧
        (stkI CC ops gv ins us).map dv = mStk (ccOf CC) (ops.map colM) (gv.map dv) ins (us.map dv)
  | [], us, hus => ⟨hus, rfl⟩
  | i :: ins, us, hus => by
    have hpush : ∀ v, Can v → (∀ x ∈ snoc us v, Can x) := by
      intro v hv x hx
      rw [snoc_eq, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hus x hx
      · exact hv
    have hsnoc : ∀ v, (snoc us v).map dv = us.map dv ++ [dv v] := by
      intro v
      rw [snoc_eq, List.map_append, List.map_singleton]
    rw [stkI_cons, mStk_cons]
    unfold pushV
    by_cases h0 : i.1 = 0
    · rw [if_pos h0, if_pos h0]
      have hv := can_getL hgv i.2.1
      have := stkI_spec hgv ins _ (hpush _ hv)
      rw [hsnoc, dv_getL] at this
      exact this
    rw [if_neg h0, if_neg h0]
    by_cases h1 : i.1 = 1
    · rw [if_pos h1, if_pos h1]
      obtain ⟨ho1, ho2⟩ := getLL_ops hD.ops i.2.1
      obtain ⟨hv, ev⟩ := mvL_spec ho1 ho2 (can_getL hus i.2.2.1)
      have := stkI_spec hgv ins _ (hpush _ hv)
      rw [hsnoc, ev, dv_getL, ← opsM_getD] at this
      exact this
    rw [if_neg h1, if_neg h1]
    by_cases h2 : i.1 = 2
    · rw [if_pos h2, if_pos h2]
      obtain ⟨hv, ev⟩ := crs_spec hD.tab (can_getL hus i.2.1) (can_getL hus i.2.2.1)
      have := stkI_spec hgv ins _ (hpush _ hv)
      rw [hsnoc, ev, dv_getL, dv_getL] at this
      exact this
    rw [if_neg h2, if_neg h2]
    exact stkI_spec hgv ins us hus

end Run

end CFSG.KS.LyFive.G2

end
