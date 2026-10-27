module

public import Certificates.Data.Kernel.D42Cls
public import CFSG.Certificates.Kernel.D4PlaneSound
import CFSG.Certificates.Kernel.D42KSound

public section

namespace CFSG.KC.D42Cls

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.KC.D4PlaneP

@[expose] def bitsE (b0 b1 b2 : Bool) : GF8 := GF8.ofNat' (b0.toNat + 2 * b1.toNat + 4 * b2.toNat)

@[expose] def laneE (a : N3) (p : Nat) : GF8 :=
  bitsE (a.1.testBit p) (a.2.1.testBit p) (a.2.2.testBit p)

@[expose] def keyV (F : List N3) (p : Nat) : Nat :=
  F.foldl (fun acc a => 8 * acc + (laneE a p).toNat) 0

theorem bitsE_xor (x0 x1 x2 y0 y1 y2 : Bool) :
    bitsE (x0 ^^ y0) (x1 ^^ y1) (x2 ^^ y2) = bitsE x0 x1 x2 + bitsE y0 y1 y2 := by
  revert x0 x1 x2 y0 y1 y2
  decide

theorem laneE_zero (p : Nat) : laneE (0, 0, 0) p = 0 := by
  simp only [laneE, Nat.zero_testBit]
  rfl

theorem laneE_x3 (a b : N3) (p : Nat) : laneE (x3 a b) p = laneE a p + laneE b p := by
  simp only [laneE, x3, Nat.testBit_xor]
  exact bitsE_xor _ _ _ _ _ _

theorem laneE_m3 (a b : N3) (p : Nat) : laneE (m3 a b) p = laneE a p * laneE b p := by
  simp only [laneE, m3, red5, Nat.testBit_xor, Nat.testBit_and]
  generalize a.1.testBit p = a0
  generalize a.2.1.testBit p = a1
  generalize a.2.2.testBit p = a2
  generalize b.1.testBit p = b0
  generalize b.2.1.testBit p = b1
  generalize b.2.2.testBit p = b2
  revert a0 a1 a2 b0 b1 b2
  decide

theorem testBit_mulBit (s b p : Nat) (hs : s < 2) :
    (s * b).testBit p = (decide (s = 1) && b.testBit p) := by
  interval_cases s <;> simp

theorem ofNat'_bits (s : Nat) : GF8.ofNat' s =
    bitsE (decide (s % 2 = 1)) (decide (s / 2 % 2 = 1)) (decide (s / 4 % 2 = 1)) := by
  have h1 : s % 2 = s % 8 % 2 := by omega
  have h2 : s / 2 % 2 = s % 8 / 2 % 2 := by omega
  have h3 : s / 4 % 2 = s % 8 / 4 % 2 := by omega
  have h0 : GF8.ofNat' s = GF8.ofNat' (s % 8) := by
    unfold GF8.ofNat'
    simp only [Nat.mod_mod]
  rw [h1, h2, h3, h0]
  have key : ∀ t < 8, GF8.ofNat' t =
      bitsE (decide (t % 2 = 1)) (decide (t / 2 % 2 = 1)) (decide (t / 4 % 2 = 1)) := by decide
  exact key _ (Nat.mod_lt _ (by decide))

theorem laneE_s3 (s : Nat) (b : N3) (p : Nat) : laneE (s3 s b) p = GF8.ofNat' s * laneE b p := by
  rw [ofNat'_bits]
  simp only [laneE, s3, s3k, Nat.testBit_xor, testBit_mulBit _ _ _ (Nat.mod_lt _ (by decide))]
  generalize decide (s % 2 = 1) = c0
  generalize decide (s / 2 % 2 = 1) = c1
  generalize decide (s / 4 % 2 = 1) = c2
  generalize b.1.testBit p = b0
  generalize b.2.1.testBit p = b1
  generalize b.2.2.testBit p = b2
  revert c0 c1 c2 b0 b1 b2
  decide

theorem laneE_dotS (p : Nat) : ∀ (l : List Nat) (m : List N3),
    laneE (dotS l m) p = ((l.zip m).map fun q => GF8.ofNat' q.1 * laneE q.2 p).sum
  | [], m => by cases m <;> simp [dotS, laneE_zero]
  | s :: l, [] => by simp [dotS, laneE_zero]
  | s :: l, b :: m => by
    simp only [dotS, laneE_x3, laneE_s3, laneE_dotS p l m]
    simp

theorem laneE_dotM (p : Nat) : ∀ (l m : List N3),
    laneE (dotM l m) p = ((l.zip m).map fun q => laneE q.1 p * laneE q.2 p).sum
  | [], m => by cases m <;> simp [dotM, laneE_zero]
  | a :: l, [] => by simp [dotM, laneE_zero]
  | a :: l, b :: m => by
    simp only [dotM, laneE_x3, laneE_m3, laneE_dotM p l m]
    simp

theorem sum_zip8 {α β : Type} (f : α × β → GF8) (l : List α) (m : List β) (dl : α) (dm : β)
    (hl : l.length = 8) (hm : m.length = 8) :
    ((l.zip m).map f).sum = f (l.getD 0 dl, m.getD 0 dm) + f (l.getD 1 dl, m.getD 1 dm) +
      f (l.getD 2 dl, m.getD 2 dm) + f (l.getD 3 dl, m.getD 3 dm) + f (l.getD 4 dl, m.getD 4 dm) +
      f (l.getD 5 dl, m.getD 5 dm) + f (l.getD 6 dl, m.getD 6 dm) + f (l.getD 7 dl, m.getD 7 dm) := by
  match l, m, hl, hm with
  | [a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7], _, _ =>
    simp [add_assoc]

theorem and_one_eq (y : Nat) : y &&& 1 = (y.testBit 0).toNat := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h]

theorem ofNat'_entP (x t : Nat) :
    GF8.ofNat' (entP x t) = bitsE (x.testBit t) (x.testBit (64 + t)) (x.testBit (128 + t)) := by
  unfold entP
  rw [and_one_eq, and_one_eq, and_one_eq]
  simp only [Nat.testBit_shiftRight, Nat.add_zero]
  generalize x.testBit t = b0
  generalize x.testBit (64 + t) = b1
  generalize x.testBit (128 + t) = b2
  revert b0 b1 b2
  decide

theorem ofNat'_toNat (e : GF8) : GF8.ofNat' e.toNat = e := by
  obtain ⟨⟨v, hv⟩⟩ := e
  simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt hv]

theorem ofNat'_entP_packA (A : Array GF8) {t : Nat} (ht : t < 64) :
    GF8.ofNat' (entP (packA A) t) = A.getD t 0 := by
  rw [ofNat'_entP, testBit_packA, testBit_packA, testBit_packA]
  have e0 : t % 64 = t := Nat.mod_eq_of_lt ht
  have e1 : (64 + t) % 64 = t := by omega
  have e2 : (128 + t) % 64 = t := by omega
  have f0 : t / 64 = 0 := by omega
  have f1 : (64 + t) / 64 = 1 := by omega
  have f2 : (128 + t) / 64 = 2 := by omega
  rw [e0, e1, e2, f0, f1, f2]
  conv_rhs => rw [← ofNat'_toNat (A.getD t 0)]
  generalize A.getD t 0 = e
  revert e
  decide

theorem getD_map_range {α : Type} (f : Nat → α) {n i : Nat} (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]

theorem length_rowsP (x : Nat) : (rowsP x).length = 8 := by simp [rowsP]

theorem getD_rowsP (x : Nat) {j : Nat} (hj : j < 8) :
    (rowsP x).getD j [] = (List.range 8).map fun l => entP x (8 * j + l) :=
  getD_map_range _ _ hj

theorem laneE_rowW (R B : Array GF8) (W : List N3) (col p : Nat) (hW : W.length = 8)
    (hWe : ∀ l < 8, laneE (W.getD l (0, 0, 0)) p = B.getD (8 * l + col) 0) (hc : col < 8)
    {j : Nat} (hj : j < 8) :
    laneE (dotS ((rowsP (packA R)).getD j []) W) p = (mulArr R B).getD (8 * j + col) 0 := by
  rw [laneE_dotS, getD_rowsP _ hj, sum_zip8 _ _ _ 0 (0, 0, 0) (by simp) hW,
    CFSG.KC.D42K.getD_mulArr R B hj hc]
  simp only [getD_map_range _ _ (by decide : (0 : Nat) < 8), getD_map_range _ _ (by decide : 1 < 8),
    getD_map_range _ _ (by decide : 2 < 8), getD_map_range _ _ (by decide : 3 < 8),
    getD_map_range _ _ (by decide : 4 < 8), getD_map_range _ _ (by decide : 5 < 8),
    getD_map_range _ _ (by decide : 6 < 8), getD_map_range _ _ (by decide : 7 < 8)]
  rw [hWe 0 (by decide), hWe 1 (by decide), hWe 2 (by decide), hWe 3 (by decide),
    hWe 4 (by decide), hWe 5 (by decide), hWe 6 (by decide), hWe 7 (by decide)]
  simp only [ofNat'_entP_packA R (by omega : 8 * j + 0 < 64), ofNat'_entP_packA R (by omega : 8 * j + 1 < 64),
    ofNat'_entP_packA R (by omega : 8 * j + 2 < 64), ofNat'_entP_packA R (by omega : 8 * j + 3 < 64),
    ofNat'_entP_packA R (by omega : 8 * j + 4 < 64), ofNat'_entP_packA R (by omega : 8 * j + 5 < 64),
    ofNat'_entP_packA R (by omega : 8 * j + 6 < 64), ofNat'_entP_packA R (by omega : 8 * j + 7 < 64)]

theorem laneE_fLanes (A R B : Array GF8) (CR : List (List N3)) (W : List N3) (col p : Nat)
    (hCR : CR.length = 8) (hCRl : ∀ i < 8, (CR.getD i []).length = 8)
    (hCRe : ∀ i < 8, ∀ j < 8, laneE ((CR.getD i []).getD j (0, 0, 0)) p = A.getD (8 * i + j) 0)
    (hW : W.length = 8) (hWe : ∀ l < 8, laneE (W.getD l (0, 0, 0)) p = B.getD (8 * l + col) 0)
    (hc : col < 8) {i : Nat} (hi : i < 8) :
    laneE ((fLanes CR W (rowsP (packA R))).getD i (0, 0, 0)) p =
      (mulArr A (mulArr R B)).getD (8 * i + col) 0 := by
  have hrow : (fLanes CR W (rowsP (packA R))).getD i (0, 0, 0) =
      dotM (CR.getD i []) ((rowsP (packA R)).map fun row => dotS row W) := by
    unfold fLanes cLanes
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  rw [hrow, laneE_dotM, sum_zip8 _ _ _ (0, 0, 0) (0, 0, 0) (hCRl i hi) (by simp [length_rowsP]),
    CFSG.KC.D42K.getD_mulArr A _ hi hc]
  have hu : ∀ j < 8, ((rowsP (packA R)).map fun row => dotS row W).getD j (0, 0, 0) =
      dotS ((rowsP (packA R)).getD j []) W := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [length_rowsP]; omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_rowsP]; omega)]
    rfl
  have hv : ∀ j < 8, laneE ((CR.getD i []).getD j (0, 0, 0)) p *
      laneE (((rowsP (packA R)).map fun row => dotS row W).getD j (0, 0, 0)) p =
      A.getD (8 * i + j) 0 * (mulArr R B).getD (8 * j + col) 0 := by
    intro j hj
    rw [hu j hj, hCRe i hi j hj, laneE_rowW R B W col p hW hWe hc hj]
  rw [hv 0 (by decide), hv 1 (by decide), hv 2 (by decide), hv 3 (by decide), hv 4 (by decide),
    hv 5 (by decide), hv 6 (by decide), hv 7 (by decide)]

theorem testBit_pieceRec (X o k : Nat) : ∀ n : Nat,
    (Nat.rec (motive := fun _ => Nat) 0
      (fun q acc => acc ||| (((X >>> (192 * q + o)) &&& 1) <<< q)) n : Nat).testBit k =
      (decide (k < n) && X.testBit (192 * k + o))
  | 0 => by simp
  | n + 1 => by
    change ((Nat.rec (motive := fun _ => Nat) 0
      (fun q acc => acc ||| (((X >>> (192 * q + o)) &&& 1) <<< q)) n : Nat) |||
        (((X >>> (192 * n + o)) &&& 1) <<< n)).testBit k = _
    rw [Nat.testBit_or, testBit_pieceRec X o k n, Nat.testBit_shiftLeft, Nat.testBit_and,
      Nat.testBit_shiftRight]
    have h1 : (1 : Nat).testBit (k - n) = decide (0 = k - n) := by
      rw [← Nat.pow_zero 2, Nat.testBit_two_pow]
    rw [h1]
    by_cases hkn : k < n
    · have : ¬ (k ≥ n) := by omega
      simp [hkn, this, show k < n + 1 by omega]
    · by_cases hk : k = n
      · subst hk
        simp
      · have : ¬ (k < n + 1) := by omega
        have h0 : ¬ (0 = k - n) := by omega
        simp [hkn, this, h0]

theorem testBit_pieceT (X o k : Nat) :
    (pieceT X o).testBit k = (decide (k < 64) && X.testBit (192 * k + o)) :=
  testBit_pieceRec X o k 64

theorem testBit_laneT (o : Nat) : ∀ (T : List Nat) (c : Nat), c < 64 * T.length →
    (laneT T o).testBit c = (T.getD (c / 64) 0).testBit (192 * (c % 64) + o)
  | [], c, hc => by simp at hc
  | X :: T, c, hc => by
    change (pieceT X o ||| (laneT T o <<< 64)).testBit c = _
    rw [Nat.testBit_or, testBit_pieceT, Nat.testBit_shiftLeft]
    by_cases h64 : c < 64
    · have hd : c / 64 = 0 := Nat.div_eq_of_lt h64
      have hm : c % 64 = c := Nat.mod_eq_of_lt h64
      have : ¬ (c ≥ 64) := by omega
      simp [h64, this, hd, hm]
    · have hc' : c - 64 < 64 * T.length := by
        simp only [List.length_cons] at hc
        omega
      rw [testBit_laneT o T (c - 64) hc']
      have hd : c / 64 = (c - 64) / 64 + 1 := by omega
      have hm : (c - 64) % 64 = c % 64 := by omega
      have : c ≥ 64 := by omega
      simp [h64, this, hd, hm]

theorem testBit_fldT (T : List Nat) (c : Nat) {k : Nat} (hk : k < 192) :
    (fldT T c).testBit k = (T.getD (c / 64) 0).testBit (192 * (c % 64) + k) := by
  rw [fldT, Nat.testBit_and, Nat.testBit_shiftRight, testBit_m192]
  simp [hk]

theorem laneOK_spec {T : List Nat} {t : Nat} {a : N3} (h : laneOK T t a = true) (ht : t < 64)
    {c : Nat} (hc : c < 64 * T.length) :
    laneE a (64 + c) = GF8.ofNat' (entP (fldT T c) t) := by
  simp only [laneOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [ofNat'_entP, testBit_fldT _ _ (by omega), testBit_fldT _ _ (by omega),
    testBit_fldT _ _ (by omega), ← testBit_laneT _ _ _ hc, ← testBit_laneT _ _ _ hc,
    ← testBit_laneT _ _ _ hc, ← h1, ← h2, ← h3, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight]
  rfl

theorem rowsAt_spec {N : Nat} {T TW : List Nat} {DP Vm : Nat} {S : List Nat} :
    ∀ (L : List (Nat × Nat × Nat × List Nat)) (b : Nat), rowsAt N T TW DP Vm S b L = true →
      ∀ k (hk : k < L.length), L[k].1 = b + k ∧ rowOK N T TW DP Vm S L[k] = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | row :: L, b, h, k, hk => by
    simp only [rowsAt, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases k with
    | zero => exact ⟨by simpa using h1, h2⟩
    | succ k =>
      have hk' : k < L.length := by
        simp only [List.length_cons] at hk
        omega
      have ih := rowsAt_spec L (b + 1) h3 k hk'
      simp only [List.getElem_cons_succ]
      exact ⟨by rw [ih.1]; omega, ih.2⟩

theorem rowsOK_spec {N : Nat} {T TW : List Nat} {DP Vm : Nat} {S : List Nat}
    {rows : List (List (Nat × Nat × Nat × List Nat))} {m : Nat}
    (h : ∀ j < m, rowsOK N T TW DP Vm S rows j = true) (hm : N ≤ 64 * m) :
    ∀ c < N, (c + 1 < N → fldT T c < fldT T (c + 1)) ∧
      (byteD DP c = 0 → fldT T c = oneP) ∧
      (byteD DP c ≠ 0 → ∃ q < N, ∃ g < S.length, byteD DP q < byteD DP c ∧
        mulP (fldT T q) (S.getD g oneP) = fldT T c) ∧
      mulP (fldT T c) (fldT TW c) = Vm ∧
      ∀ g < S.length, ∃ c' < N, mulP (fldT T c) (S.getD g oneP) = fldT T c' := by
  intro c hc
  have hj : c / 64 < m := by omega
  have h' := h (c / 64) hj
  simp only [rowsOK, Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨hlen, hat⟩ := h'
  have hk : c % 64 < (rows.getD (c / 64) []).length := by
    rw [hlen]
    omega
  obtain ⟨hc1, hok⟩ := rowsAt_spec _ _ hat (c % 64) hk
  generalize (rows.getD (c / 64) [])[c % 64] = row at hc1 hok
  obtain ⟨c0, p, g, cl⟩ := row
  have hrc : c0 = c := by
    change c0 = _ + _ at hc1
    omega
  subst hrc
  simp only [rowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true,
    List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hG⟩, hH⟩ := hok
  refine ⟨fun h1 => hD.resolve_left (by omega), fun hz => ?_, fun hz => ?_, hF, fun g' hg' => ?_⟩
  · simp only [hz, beq_self_eq_true, cond_true, beq_iff_eq] at hE
    exact hE
  · have hz' : (byteD DP c0 == 0) = false := by simpa using hz
    rw [hz', cond_false] at hE
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hE
    exact ⟨p, hB, g, hC, hE.1, hE.2⟩
  · have hz : g' < (S.zip cl).length := by
      rw [List.length_zip, hG]
      omega
    have hq := hH _ (List.getElem_mem hz)
    rw [List.getElem_zip] at hq
    refine ⟨cl[g']'(by omega), hq.1, ?_⟩
    rw [List.getD_eq_getElem _ _ hg']
    exact hq.2

theorem crOK_spec {T : List Nat} {CR : List (List N3)} (h : ∀ i < 8, crOK T CR i = true) :
    ∀ i < 8, (CR.getD i []).length = 8 ∧ ∀ c < 64 * T.length, ∀ j < 8,
      laneE ((CR.getD i []).getD j (0, 0, 0)) (64 + c) = GF8.ofNat' (entP (fldT T c) (8 * i + j)) := by
  intro i hi
  have hi' := h i hi
  simp only [crOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hi'
  obtain ⟨hl, hall⟩ := hi'
  refine ⟨hl, fun c hc j hj => ?_⟩
  have hjl : j < ((List.range 8).zip (CR.getD i [])).length := by
    rw [List.length_zip, List.length_range, hl]
    omega
  have hmem := hall _ (List.getElem_mem hjl)
  rw [List.getElem_zip, List.getElem_range] at hmem
  have hj' : j < (CR.getD i []).length := hl ▸ hj
  have e : (CR.getD i []).getD j (0, 0, 0) = (CR.getD i [])[j]'hj' := by
    rw [List.getD_eq_getElem]
  rw [e]
  exact laneOK_spec hmem (by omega) hc

theorem wOK_spec {TW : List Nat} {W : List N3} {col : Nat} (h : wOK TW W col = true)
    (hc : col < 8) :
    W.length = 8 ∧ ∀ c < 64 * TW.length, ∀ l < 8,
      laneE (W.getD l (0, 0, 0)) (64 + c) = GF8.ofNat' (entP (fldT TW c) (8 * l + col)) := by
  simp only [wOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hl, hall⟩ := h
  refine ⟨hl, fun c hcT l hlt => ?_⟩
  have hjl : l < ((List.range 8).zip W).length := by
    rw [List.length_zip, List.length_range, hl]
    omega
  have hmem := hall _ (List.getElem_mem hjl)
  rw [List.getElem_zip, List.getElem_range] at hmem
  have hl' : l < W.length := hl ▸ hlt
  rw [List.getD_eq_getElem _ _ hl']
  exact laneOK_spec hmem (by omega) hcT

theorem bitsE_inj (a0 a1 a2 b0 b1 b2 : Bool) (h : bitsE a0 a1 a2 = bitsE b0 b1 b2) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  revert a0 a1 a2 b0 b1 b2
  decide

theorem toNat_bitsE (b0 b1 b2 : Bool) :
    (bitsE b0 b1 b2).toNat = b0.toNat + 2 * b1.toNat + 4 * b2.toNat := by
  revert b0 b1 b2
  decide

theorem testBit_O (N k : Nat) :
    (((1 <<< N) - 1) <<< 64).testBit k = (decide (k ≥ 64) && decide (k - 64 < N)) := by
  rw [Nat.testBit_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem testBit_neq1 {O k : Nat} (hO : O.testBit k = true) (a : N3) (e : Nat)
    (h : laneE a k = GF8.ofNat' e) : (neq1 O a e).testBit k = false := by
  rw [ofNat'_bits, laneE] at h
  obtain ⟨h1, h2, h3⟩ := bitsE_inj _ _ _ _ _ _ h
  simp only [neq1, Nat.testBit_or, Nat.testBit_xor, testBit_mulBit (e % 2) O k (Nat.mod_lt _ (by decide)),
    testBit_mulBit (e / 2 % 2) O k (Nat.mod_lt _ (by decide)),
    testBit_mulBit (e / 4 % 2) O k (Nat.mod_lt _ (by decide)), hO, h1, h2, h3]
  simp

theorem testBit_neqL {O k : Nat} (hO : O.testBit k = true) : ∀ (F : List N3) (fr : List Nat),
    (∀ e < F.length, laneE (F.getD e (0, 0, 0)) k = GF8.ofNat' (fr.getD e 0)) →
      (neqL O F fr).testBit k = false
  | [], fr, _ => by cases fr <;> simp [neqL]
  | a :: F, [], _ => by simp [neqL]
  | a :: F, x :: fr, h => by
    change (neq1 O a x ||| neqL O F fr).testBit k = false
    rw [Nat.testBit_or, testBit_neq1 hO a x (by simpa using h 0 (by simp)),
      testBit_neqL hO F fr fun e he => by simpa using h (e + 1) (by simp; omega)]
    rfl

theorem mem_of_testBit_maskOf (c : Nat) : ∀ P : List Nat, (maskOf P).testBit (64 + c) = true → c ∈ P
  | [], h => by simp [maskOf] at h
  | p :: P, h => by
    change (maskOf P ||| (1 <<< (64 + p))).testBit (64 + c) = true at h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h
    rcases h with h | h
    · exact List.mem_cons_of_mem _ (mem_of_testBit_maskOf c P h)
    · have : c = p := by simp at h; omega
      exact this ▸ List.mem_cons_self

@[expose] def pfxV (ps : List Nat) (a k : Nat) : Nat := ps.foldl (fun acc p => 2 * acc + (p.testBit k).toNat) a

theorem pfxV_cons (p : Nat) (ps : List Nat) (a k : Nat) :
    pfxV (p :: ps) a k = pfxV ps (2 * a + (p.testBit k).toNat) k := rfl

theorem pfxV_lt : ∀ (ps : List Nat) {a a' : Nat} (k k' : Nat), a < a' → pfxV ps a k < pfxV ps a' k'
  | [], _, _, _, _, h => h
  | p :: ps, a, a', k, k', h => by
    rw [pfxV_cons, pfxV_cons]
    apply pfxV_lt ps k k'
    have := Bool.toNat_le (p.testBit k)
    omega

theorem pfxV_planes (k : Nat) : ∀ (F : List N3) (a : Nat),
    pfxV (planes F) a k = F.foldl (fun acc x => 8 * acc + (laneE x k).toNat) a
  | [], _ => rfl
  | x :: F, a => by
    simp only [planes, pfxV_cons, List.foldl_cons]
    rw [pfxV_planes k F]
    congr 1
    rw [laneE, toNat_bitsE]
    omega

theorem minS_spec : ∀ (ps : List Nat) (M acc : Nat), M ≠ 0 →
    (∃ k, M.testBit k = true ∧ pfxV ps acc k = minS ps M acc) ∧
      ∀ k, M.testBit k = true → minS ps M acc ≤ pfxV ps acc k
  | [], M, acc, hM => by
    obtain ⟨k, hk⟩ := Nat.exists_testBit_of_ne_zero hM
    exact ⟨⟨k, hk, rfl⟩, fun _ _ => Nat.le_refl _⟩
  | p :: ps, M, acc, hM => by
    have hbit : ∀ k, (M ^^^ (M &&& p)).testBit k = (M.testBit k && !p.testBit k) := by
      intro k
      rw [Nat.testBit_xor, Nat.testBit_and]
      cases M.testBit k <;> cases p.testBit k <;> rfl
    by_cases hz : M ^^^ (M &&& p) = 0
    · have hmin : minS (p :: ps) M acc = minS ps M (2 * acc + 1) := by
        simp only [minS, hz, beq_self_eq_true, cond_true]
      have hpf : ∀ k, M.testBit k = true → pfxV (p :: ps) acc k = pfxV ps (2 * acc + 1) k := by
        intro k hk
        have h0 := hbit k
        rw [hz, Nat.zero_testBit, hk] at h0
        have hp : p.testBit k = true := by
          revert h0
          cases p.testBit k <;> simp
        rw [pfxV_cons, hp]
        rfl
      obtain ⟨⟨k, hk, he⟩, hle⟩ := minS_spec ps M (2 * acc + 1) hM
      rw [hmin]
      exact ⟨⟨k, hk, by rw [hpf k hk, he]⟩, fun k' hk' => by rw [hpf k' hk']; exact hle k' hk'⟩
    · have hmin : minS (p :: ps) M acc = minS ps (M ^^^ (M &&& p)) (2 * acc) := by
        have hf : (M ^^^ (M &&& p) == 0) = false := by simpa using hz
        simp only [minS, hf, cond_false]
      obtain ⟨⟨k, hk, he⟩, hle⟩ := minS_spec ps _ (2 * acc) hz
      rw [hbit, Bool.and_eq_true, Bool.not_eq_true'] at hk
      rw [hmin]
      refine ⟨⟨k, hk.1, ?_⟩, fun k' hk' => ?_⟩
      · rw [pfxV_cons, hk.2, ← he]
        rfl
      · cases hpk : p.testBit k' with
        | false =>
          have hm : (M ^^^ (M &&& p)).testBit k' = true := by rw [hbit, hk', hpk]; rfl
          rw [pfxV_cons, hpk]
          exact hle k' hm
        | true =>
          rw [pfxV_cons, hpk, ← he]
          exact Nat.le_of_lt (pfxV_lt ps k k' (by simp))

theorem sweepK_spec {N : Nat} {P : List Nat} {key : Nat} {F : List N3} {fr : List Nat}
    (h : sweepK (((1 <<< N) - 1) <<< 64) P key F fr = true) (hl : F.length = fr.length) :
    (∀ c < N, (∀ e < F.length, laneE (F.getD e (0, 0, 0)) (64 + c) = GF8.ofNat' (fr.getD e 0)) →
      c ∈ P) ∧
    (0 < N → (∃ c < N, keyV F (64 + c) = key) ∧ ∀ c < N, key ≤ keyV F (64 + c)) := by
  simp only [sweepK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hz, hkey⟩ := h
  have hOc : ∀ c < N, (((1 <<< N) - 1) <<< 64).testBit (64 + c) = true := by
    intro c hc
    rw [testBit_O]
    simp
    omega
  have hkV : ∀ k, keyV F k = pfxV (planes F) 0 k := fun k => (pfxV_planes k F 0).symm
  refine ⟨fun c hc hall => ?_, fun hN => ?_⟩
  · have h0 := congrArg (fun x => Nat.testBit x (64 + c)) hz
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, hOc c hc,
      testBit_neqL (hOc c hc) F fr hall] at h0
    apply mem_of_testBit_maskOf
    revert h0
    cases (maskOf P).testBit (64 + c) <;> simp
  · have hO : ((1 <<< N) - 1) <<< 64 ≠ 0 := by
      intro h0
      have h1 := hOc 0 hN
      rw [h0, Nat.zero_testBit] at h1
      exact Bool.false_ne_true h1
    obtain ⟨⟨k, hk, he⟩, hle⟩ := minS_spec (planes F) _ 0 hO
    rw [hkey] at he hle
    rw [testBit_O] at hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    refine ⟨⟨k - 64, by omega, ?_⟩, fun c hc => ?_⟩
    · rw [hkV, Nat.add_sub_cancel' hk.1, he]
    · rw [hkV]
      exact hle _ (hOc c hc)

end CFSG.KC.D42Cls

end
