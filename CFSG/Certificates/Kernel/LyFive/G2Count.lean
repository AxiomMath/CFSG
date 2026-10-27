module

public import CFSG.Certificates.Kernel.LyFive.G2Sound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.LyFive.G2

open CFSG.KC.LyG2 CFSG.KC.Enum CFSG.KS.SporSch.LySev CFSG.KS.SporSch.LySvC CFSG.KS.SporSch.LyLoop
open Matrix

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem nmod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem ndiv_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem dec_eq (n : ℕ) : dec n = laneSum (fun L => n / 5 ^ L % 5) 7 := by
  unfold dec laneSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, shl_eq, nmod_eq, ndiv_eq]
  norm_num
  ring

theorem dec_can (n : ℕ) : Can (dec n) := by
  rw [dec_eq]
  exact can_laneSum fun L _ => Nat.mod_lt _ (by norm_num)

theorem dv_dec (n : ℕ) (i : Fin 7) : dv (dec n) i = ((n / 5 ^ i.val % 5 : ℕ) : ZMod 5) := by
  rw [dec_eq, dv_laneSum fun L _ => by have := Nat.mod_lt (n / 5 ^ L) (show 0 < 5 by norm_num); omega]

theorem digits_eq : ∀ (k n m : ℕ), n < 5 ^ k → m < 5 ^ k →
    (∀ L < k, n / 5 ^ L % 5 = m / 5 ^ L % 5) → n = m
  | 0, n, m, hn, hm, _ => by simp at hn hm; omega
  | k + 1, n, m, hn, hm, h => by
    have h0 := h 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    have hq : n / 5 = m / 5 := by
      refine digits_eq k (n / 5) (m / 5) (by rw [pow_succ] at hn; omega) (by rw [pow_succ] at hm; omega)
        fun L hL => ?_
      have := h (L + 1) (by omega)
      rwa [pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    omega

theorem dec_inj {n m : ℕ} (hn : n < 78125) (hm : m < 78125) (h : dv (dec n) = dv (dec m)) : n = m := by
  refine digits_eq 7 n m (by norm_num; omega) (by norm_num; omega) fun L hL => ?_
  have e := congrFun h ⟨L, hL⟩
  rw [dv_dec, dv_dec] at e
  have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
  rwa [Nat.mod_mod, Nat.mod_mod] at this

theorem dec_surj (w : V) : ∃ n < 78125, dv (dec n) = w := by
  classical
  have hinj : Set.InjOn (fun n => dv (dec n)) (Finset.range 78125 : Set ℕ) := by
    intro a ha b hb e
    exact dec_inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) e
  have hcard : ((Finset.range 78125).image fun n => dv (dec n)).card = Fintype.card V := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    simp
  have huniv := Finset.eq_univ_of_card _ hcard
  have hw : w ∈ (Finset.range 78125).image fun n => dv (dec n) := by rw [huniv]; exact Finset.mem_univ w
  obtain ⟨n, hn, e⟩ := Finset.mem_image.1 hw
  exact ⟨n, Finset.mem_range.1 hn, e⟩

theorem foldr_count_aux (g : ℕ → ℕ) : ∀ (l : List ℕ) (s : ℕ),
    l.foldr (fun i acc => Nat.add acc (g i)) s = s + (l.map g).sum
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldr_cons, foldr_count_aux g l s, List.map_cons, List.sum_cons]
    change s + _ + g a = _
    ring

theorem foldr_count (p : ℕ → Bool) (n : ℕ) :
    (List.range n).foldr (fun i acc => Nat.add acc (nIf(p i, nat_lit 1, nat_lit 0))) 0 =
      ((Finset.range n).filter fun i => p i = true).card := by
  rw [foldr_count_aux (fun i => nIf(p i, nat_lit 1, nat_lit 0)), Nat.zero_add, Finset.card_filter]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, nIf_eqP]

theorem cntBlk_eq (CC : List (List ℕ)) (TT : List ℕ) (ops : List (List ℕ)) (F : List ℕ)
    (ins : List (ℕ × ℕ × ℕ × List ℕ)) (k : ℕ) :
    cntBlk CC TT ops F ins k = ((Finset.range 3125).filter fun i =>
      passW CC TT ops F ins (dec (3125 * k + i)) = true).card := by
  unfold cntBlk
  rw [foldN_eqP]
  exact foldr_count (fun i => passW CC TT ops F ins (dec (3125 * k + i))) 3125

theorem card_filter_blocks (p : ℕ → Prop) [DecidablePred p] : ∀ (m : ℕ),
    ((Finset.range (3125 * m)).filter p).card =
      ∑ k ∈ Finset.range m, ((Finset.range 3125).filter fun i => p (3125 * k + i)).card
  | 0 => by simp
  | m + 1 => by
    have e : 3125 * (m + 1) = 3125 * m + 3125 := by ring
    rw [Finset.sum_range_succ, ← card_filter_blocks p m, e, Finset.card_filter, Finset.card_filter,
      Finset.card_filter, Finset.sum_range_add]

theorem card_passSet_eq {CC : List (List ℕ)} {TT : List ℕ} {ops : List (List ℕ)}
    (hD : DataOK CC TT ops) {F : List ℕ} (hF : ∀ x ∈ F, Can x) {ins : List (ℕ × ℕ × ℕ × List ℕ)}
    (hins : insOK ins = true) :
    (passSet (ccOf CC) (ops.map colM) (F.map dv) ins).card =
      ∑ k ∈ Finset.range 25, cntBlk CC TT ops F ins k := by
  classical
  have hins' := (insOK_iff ins).1 hins
  have hpass : ∀ n, passW CC TT ops F ins (dec n) = true ↔
      mRun (ccOf CC) (ops.map colM) (F.map dv ++ [dv (dec n)]) ins [] := by
    intro n
    have hgv : ∀ x ∈ snoc F (dec n), Can x := can_snoc hF (dec_can n)
    have := runI_iff hD hgv ins hins' [] (fun x hx => absurd hx List.not_mem_nil)
    rw [show passW CC TT ops F ins (dec n) = runI CC TT ops (snoc F (dec n)) ins [] from rfl, this,
      snoc_eq, List.map_append, List.map_singleton, List.map_nil]
  simp only [cntBlk_eq]
  rw [← card_filter_blocks (fun n => passW CC TT ops F ins (dec n) = true) 25]
  have himg : passSet (ccOf CC) (ops.map colM) (F.map dv) ins =
      ((Finset.range 78125).filter fun n => passW CC TT ops F ins (dec n) = true).image
        fun n => dv (dec n) := by
    ext w
    rw [mem_passSet, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨n, hn, rfl⟩ := dec_surj w
      exact ⟨n, Finset.mem_filter.2 ⟨Finset.mem_range.2 hn, (hpass n).2 h⟩, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact (hpass n).1 (Finset.mem_filter.1 hn).2
  rw [himg, Finset.card_image_of_injOn]
  intro a ha b hb e
  exact dec_inj (Finset.mem_range.1 (Finset.mem_filter.1 ha).1)
    (Finset.mem_range.1 (Finset.mem_filter.1 hb).1) e

theorem matOK_iff (cols : List ℕ) : matOK cols = true ↔ cols.length ≤ 7 ∧ ∀ x ∈ cols, Can x := by
  change bAnd(Nat.ble (lenL cols) 7, redL cols) = true ↔ _
  rw [bAnd_eqP, Bool.and_eq_true, Nat.ble_eq, lenL_eq, redL_iff]

theorem lenLL_eq (l : List (List ℕ)) : lenLL l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Nat.succ (lenLL l) = _
    rw [ih]
    rfl

theorem matsOK_iff (l : List (List ℕ)) :
    matsOK l = true ↔ ∀ m ∈ l, m.length ≤ 7 ∧ ∀ x ∈ m, Can x := by
  induction l with
  | nil => simp [matsOK]
  | cons m l ih =>
    change bAnd(matOK m, matsOK l) = true ↔ _
    rw [bAnd_eqP, Bool.and_eq_true, matOK_iff, ih, List.forall_mem_cons]

theorem e_lane (i : ℕ) (hi : i < 7) :
    Nat.shiftLeft 1 (Nat.mul 20 i) = laneSum (fun L => if L = i then 1 else 0) 7 := by
  unfold laneSum
  rw [shl_eq, Nat.one_mul]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
    (fun h => absurd (Finset.mem_range.2 hi) h)]
  simp only [if_pos, Nat.one_mul]
  rfl

theorem e_lt (i L : ℕ) : (if L = i then 1 else 0) < 5 := by
  by_cases h : L = i
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    norm_num

theorem dv_e (i : Fin 7) : dv (Nat.shiftLeft 1 (Nat.mul 20 i.val)) = Pi.single i 1 := by
  rw [e_lane i.val i.isLt]
  funext j
  rw [dv_laneSum (fun L _ => Nat.lt_of_lt_of_le (e_lt i.val L) (by norm_num))]
  by_cases h : j = i
  · subst h
    simp
  · rw [if_neg (fun e => h (Fin.ext e)), Pi.single_apply, if_neg h]
    rfl

theorem can_e (i : ℕ) (hi : i < 7) : Can (Nat.shiftLeft 1 (Nat.mul 20 i)) := by
  rw [e_lane i hi]
  exact can_laneSum fun L _ => e_lt i L

theorem trace_Lm (cc : Fin 7 → Fin 7 → V) (i j : Fin 7) :
    Tβ cc i j = ∑ k : Fin 7, cr cc (Pi.single i 1) (cc j k) k := by
  change β cc (Pi.single i 1) (Pi.single j 1) = _
  rw [β, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply]
  have h := congrFun (Matrix.mulVec_single_one (Lm cc (Pi.single i 1) * Lm cc (Pi.single j 1)) k) k
  rw [← mulVec_mulVec, Lm_mulVec, Lm_mulVec, cr_single] at h
  rw [h]
  rfl

theorem dataOK_of {CC : List (List ℕ)} {TT : List ℕ} {ops : List (List ℕ)} (h : dataChk CC TT = true)
    (hops : matsOK ops = true) : DataOK CC TT ops := by
  change bAnd(Nat.ble (lenLL CC) 7, bAnd(matsOK CC, bAnd(matOK TT, tChk CC TT))) = true at h
  simp only [bAnd_eqP, Bool.and_eq_true, Nat.ble_eq, lenLL_eq, matsOK_iff, matOK_iff] at h
  obtain ⟨hl, hrows, ⟨hTl, hTc⟩, ht⟩ := h
  have hTab : TabOK CC := And.intro hl hrows
  refine ⟨hTab, hTc, hTl, ?_, fun o ho => ⟨((matsOK_iff ops).1 hops o ho).2,
    ((matsOK_iff ops).1 hops o ho).1⟩⟩
  ext r t
  unfold tChk at ht
  have h1 := CFSG.KS.allN_spec ht (7 * r.val + t.val)
    (by change 7 * r.val + t.val < 49; have := r.isLt; have := t.isLt; omega)
  rw [nmod_eq, ndiv_eq, show (7 * r.val + t.val) % 7 = t.val by omega,
    show (7 * r.val + t.val) / 7 = r.val by omega, Nat.beq_eq, nmod_eq] at h1
  have hrow : ∀ k, Can (getL (getLL CC t.val) k) := by
    intro k
    rw [getLL_eq]
    by_cases ht' : t.val < CC.length
    · rw [List.getD_eq_getElem _ _ ht']
      exact can_getL (hrows _ (List.getElem_mem ht')).2 k
    · rw [List.getD_eq_default _ _ (by omega)]
      exact can_getL (fun x hx => absurd hx List.not_mem_nil) k
  have htr : trK CC r.val t.val = ∑ k ∈ Finset.range 7,
      ln (crs CC (Nat.shiftLeft 1 (Nat.mul 20 r.val)) (getL (getLL CC t.val) k)) k := by
    unfold trK
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.add_eq]
    ring
  change dv (getL TT t.val) r = _
  rw [dv, h1, ZMod.natCast_mod, htr, Nat.cast_sum, trace_Lm,
    ← Fin.sum_univ_eq_sum_range (fun k => ((ln (crs CC (Nat.shiftLeft 1 (Nat.mul 20 r.val))
      (getL (getLL CC t.val) k)) k : ℕ) : ZMod 5)) 7]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := (crs_spec hTab (can_e r.val r.isLt) (hrow k.val)).2
  rw [dv_e] at this
  have e := congrFun this k
  rw [dv] at e
  rw [e]
  rfl

theorem dropL_eq {α : Type} : ∀ (n : ℕ) (l : List α), dropL n l = l.drop n
  | 0, l => rfl
  | n + 1, [] => by
    change dropL n [] = _
    rw [dropL_eq n []]
    simp
  | n + 1, a :: l => by
    change dropL n l = _
    rw [dropL_eq n l]
    rfl

theorem takeL_eq {α : Type} : ∀ (n : ℕ) (l : List α), takeL n l = l.take n
  | n, [] => by cases n <;> rfl
  | 0, a :: l => rfl
  | n + 1, a :: l => by
    change a :: takeL n l = _
    rw [takeL_eq n l]
    rfl

theorem allL_iff {α : Type} (l : List α) (p : α → Bool) : allL l p = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp [allL]
  | cons a l ih =>
    change bAnd(p a, allL l p) = true ↔ _
    rw [bAnd_eqP, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem lenA_eq {α : Type} (l : List α) : lenA l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Nat.succ (lenA l) = _
    rw [ih]
    rfl

theorem blocks_all {α : Type} [Inhabited α] {l : List α} {p : α → Bool} {nb : ℕ}
    (h : ∀ k < nb, allL (takeL 150 (dropL (Nat.mul 150 k) l)) p = true) :
    ∀ i < l.length, i < 150 * nb → p l[i]! = true := by
  intro i hi hb
  have hk := h (i / 150) (by omega)
  rw [allL_iff, takeL_eq, dropL_eq] at hk
  apply hk
  have e : l[i]! = (List.take 150 (List.drop (Nat.mul 150 (i / 150)) l))[i % 150]'(by
      rw [List.length_take, List.length_drop]
      change i % 150 < min 150 (l.length - 150 * (i / 150))
      have := Nat.mod_lt i (show 0 < 150 by norm_num)
      have := Nat.div_add_mod i 150
      omega) := by
    rw [List.getElem_take, List.getElem_drop, getElem!_pos l i hi]
    congr 1
    change i = 150 * (i / 150) + i % 150
    omega
  rw [e]
  exact List.getElem_mem _

theorem keysInc_spec {b : ℕ} : ∀ {l : List (List ℕ × List ℕ)} (prev : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun w _ ih prev => strictB (mvL w.1 b) (fun k => bAnd(Nat.blt prev k, ih k))) l prev = true →
      (∀ i < l.length, prev < mvL l[i]!.1 b) ∧
      ∀ i < l.length, ∀ j < l.length, i < j → mvL l[i]!.1 b < mvL l[j]!.1 b
  | [], _, _ => ⟨fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp)⟩
  | w :: l, prev, h => by
    change strictB (mvL w.1 b) (fun k => bAnd(Nat.blt prev k,
      List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
        (fun w _ ih prev => strictB (mvL w.1 b) (fun k => bAnd(Nat.blt prev k, ih k))) l k)) = true at h
    rw [strictB_eqB, bAnd_eqP, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := keysInc_spec (mvL w.1 b) h2
    have hget : ∀ i (hi : i < l.length), (w :: l)[i + 1]! = l[i]! := by
      intro i hi
      rw [getElem!_pos (w :: l) (i + 1) (by simp; omega), getElem!_pos l i hi]
      rfl
    have hget0 : (w :: l)[0]! = w := by
      rw [getElem!_pos (w :: l) 0 (by simp)]
      rfl
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · rcases i with _ | i
      · rw [hget0]
        exact h1
      · rw [hget i (by simp at hi; omega)]
        exact Nat.lt_trans h1 (ih1 i (by simp at hi; omega))
    · rcases j with _ | j
      · omega
      · rw [hget j (by simp at hj; omega)]
        rcases i with _ | i
        · rw [hget0]
          exact ih1 j (by simp at hj; omega)
        · rw [hget i (by simp at hi; omega)]
          exact ih2 i (by simp at hi; omega) j (by simp at hj; omega) (by omega)

end CFSG.KS.LyFive.G2

end
