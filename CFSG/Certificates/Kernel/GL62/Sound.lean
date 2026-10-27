module

public import Certificates.Data.Kernel.GL62.Check
public import CFSG.Certificates.Kernel.GL62.LanesSound

public section

namespace CFSG.KC.GL62

open CFSG.OddStandard.AltStdSmall4.GL62 CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

theorem andB_gl (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_gl (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_gl (a : Bool) : notB a = !a := by cases a <;> rfl

theorem letB_gl (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

theorem letN_gl (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem beq_gl {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

theorem blt_gl {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem ble_gl {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b := by rw [Nat.ble_eq]

theorem allK_gl {α : Type} (l : List α) (f : α → Bool) : allK l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change andB (f x) (allK t f) = _
    rw [andB_gl, ih, List.all_cons]

theorem anyK_gl {α : Type} (l : List α) (f : α → Bool) : anyK l f = l.any f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change orB (f x) (anyK t f) = _
    rw [orB_gl, ih, List.any_cons]

theorem allL_gl (l : List ℕ) (f : ℕ → Bool) : allL l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change andB (f x) (allL t f) = _
    rw [andB_gl, ih, List.all_cons]

theorem nthK_gl {α : Type} (l : List α) (d : α) (i : ℕ) : nthK l d i = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [List.getD_cons_succ, ← ih]
      rfl

theorem lenK_gl {α : Type} (l : List α) : lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change Nat.succ (lenK t) = _
    rw [ih, List.length_cons]

theorem lenN_gl (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change Nat.succ (lenN t) = _
    rw [ih, List.length_cons]

theorem appK_gl {α : Type} (l ih : List α) :
    List.rec (motive := fun _ => List α) ih (fun x _ ih2 => List.cons x ih2) l = l ++ ih := by
  induction l with
  | nil => rfl
  | cons x t h => rw [List.cons_append, ← h]

theorem flatK_gl {α : Type} (L : List (List α)) : flatK L = L.flatten := by
  induction L with
  | nil => rfl
  | cons l t ih =>
    change List.rec (motive := fun _ => List α) (flatK t) (fun x _ ih2 => List.cons x ih2) l = _
    rw [appK_gl, ih, List.flatten_cons]

theorem fstK_gl {β : Type} (l : List (ℕ × β)) : fstK l = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    change a :: fstK t = _
    rw [ih]
    rfl

theorem headsK_gl (GD : List (ℕ × List ℕ)) : headsK GD = GD.map fun e => e.2.getD 0 0 := by
  induction GD with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨r, O⟩ := x
    change nthK O 0 0 :: headsK t = _
    rw [nthK_gl, ih]
    rfl

theorem depthsK_gl (BT : List (ℕ × ℕ × ℕ)) : depthsK BT = BT.map fun e => e.2.2 := by
  induction BT with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨a, b, c⟩ := x
    change c :: depthsK t = _
    rw [ih]
    rfl

theorem memN_gl (x : ℕ) (l : List ℕ) : memN x l = true ↔ x ∈ l := by
  unfold memN
  rw [letB_gl]
  induction l with
  | nil => exact iff_of_false Bool.false_ne_true (by simp)
  | cons z t ih =>
    change orB (Nat.beq x z) _ = true ↔ _
    rw [orB_gl, Bool.or_eq_true, beq_gl, ih, List.mem_cons]

theorem nodupN_gl (l : List ℕ) : nodupN l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupN]
  | cons z t ih =>
    change andB (notB (memN z t)) (nodupN t) = true ↔ _
    rw [andB_gl, notB_gl, Bool.and_eq_true, Bool.not_eq_true', ih, List.nodup_cons,
      Bool.eq_false_iff, ne_eq, memN_gl]

theorem T36_eq : T36 = 2 ^ 36 := by norm_num [T36]

theorem incK_gl : ∀ (lo : ℕ) (l : List ℕ), incK lo l = true →
    (∀ x ∈ l, lo < x ∧ x < 2 ^ 36) ∧ l.Pairwise (· < ·) := by
  intro lo l
  induction l generalizing lo with
  | nil => intro _; simp
  | cons x t ih =>
    intro h
    change andB (Nat.blt lo x) (andB (Nat.blt x T36) (incK x t)) = true at h
    simp only [andB_gl, Bool.and_eq_true, blt_gl, T36_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := ih x h3
    refine ⟨fun y hy => ?_, List.pairwise_cons.2 ⟨fun y hy => (ih1 y hy).1, ih2⟩⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨h1, h2⟩
    · exact ⟨h1.trans (ih1 y hy).1, (ih1 y hy).2⟩

theorem zipK_gl {α β : Type} (f : ℕ → α → β → Bool) : ∀ (l : List α) (m : List β) (i₀ : ℕ),
    zipK l m i₀ f = true → l.length = m.length ∧
      ∀ i (h : i < l.length) (h' : i < m.length), f (i₀ + i) l[i] m[i] = true := by
  intro l
  induction l with
  | nil =>
    intro m i₀ h
    cases m with
    | nil => exact ⟨rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩
    | cons y t => exact absurd h Bool.false_ne_true
  | cons x t ih =>
    intro m i₀ h
    cases m with
    | nil => exact absurd h Bool.false_ne_true
    | cons y m =>
      change andB (f i₀ x y) (letB (Nat.succ i₀) fun j => zipK t m j f) = true at h
      rw [andB_gl, letB_gl, Bool.and_eq_true] at h
      obtain ⟨ih1, ih2⟩ := ih m _ h.2
      refine ⟨by simp [ih1], fun i hi hi' => ?_⟩
      cases i with
      | zero => exact h.1
      | succ i =>
        have := ih2 i (by simpa using hi) (by simpa using hi')
        have e : i₀ + (i + 1) = Nat.succ i₀ + i := by omega
        rw [e]
        exact this

theorem bitsK_gl (l : List ℕ) (n : ℕ) : (bitsK l).testBit n = true ↔ n ∈ l := by
  induction l with
  | nil => simp [bitsK]
  | cons p t ih =>
    change ((1 <<< p) ||| bitsK t).testBit n = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih,
      List.mem_cons, decide_eq_true_iff, eq_comm]

theorem bitK_gl (m b : ℕ) : bitK m b = m.testBit b := by
  unfold bitK
  have e : Nat.land m (Nat.shiftLeft 1 b) = m &&& 2 ^ b := by
    rw [← Nat.one_shiftLeft]
    rfl
  rw [e]
  cases h : m.testBit b with
  | false =>
    have : m &&& 2 ^ b = 0 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : b = i
      · subst hi
        simp [h]
      · simp [hi]
    rw [this]
    rfl
  | true =>
    have h1 : (m &&& 2 ^ b).testBit b = true := by
      rw [Nat.testBit_and, h, Nat.testBit_two_pow_self]
      rfl
    have hne : m &&& 2 ^ b ≠ 0 := fun h0 => by
      rw [h0, Nat.zero_testBit] at h1
      exact Bool.false_ne_true h1
    exact blt_gl.2 (Nat.pos_of_ne_zero hne)

theorem lettersK_gl {w : List ℕ} (h : lettersK w = true) : ∀ a ∈ w, a ≤ 336 := by
  unfold lettersK at h
  rw [allL_gl, List.all_eq_true] at h
  exact fun a ha => ble_gl.1 (h a ha)

@[expose] def letterV (BL : List ℕ) (g a : ℕ) : ℕ := if a = 0 then g else BL.getD (a - 1) 0

@[expose] def wordV (BL : List ℕ) (g : ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc a => Code.mul acc (letterV BL g a)) Code.one

@[expose] def conjB (BL BIL : List ℕ) (k r : ℕ) : ℕ :=
  Code.mul (Code.mul (BL.getD k 0) r) (BIL.getD k 0)

@[expose] def stabB (BL BIL : List ℕ) (r : ℕ) : ℕ :=
  ((List.range 336).filter fun k => conjB BL BIL k r = r).length

@[expose] def BadW (BL : List ℕ) (y : ℕ) (w : List ℕ) : Prop :=
  (∀ a ∈ w, a ≤ 336) ∧ Code.mul (wordV BL y w) 38959071361 = Code.mul 38959071361 (wordV BL y w) ∧
    blkK (wordV BL y w) = false

@[expose] def rep (GD : List (ℕ × List ℕ)) (p : ℕ) : ℕ := (GD.getD p (0, [])).1

@[expose] def orbL (GD : List (ℕ × List ℕ)) (p : ℕ) : List ℕ := (GD.getD p (0, [])).2

@[expose] def tab (T : List (List ℕ)) (a b : ℕ) : ℕ := (T.getD a []).getD b 0

@[expose] def memOf (m : ℕ) : List ℕ := (List.range 17).filter m.testBit

open CFSG.KC.GL62.LS in
theorem letterK_gl {BL : List ℕ} (hBL : ∀ x ∈ BL, x < 2 ^ 64) (g a : ℕ) :
    letterK (packL BL) g a = letterV BL g a := by
  cases a with
  | zero => rfl
  | succ a =>
    change laneK (packL BL) a = _
    rw [laneK_packL hBL]
    rfl

open CFSG.KC.GL62.LS in
theorem wordK_gl {BL : List ℕ} (hBL : ∀ x ∈ BL, x < 2 ^ 64) (g : ℕ) (w : List ℕ) :
    wordK (packL BL) g w = wordV BL g w := by
  unfold wordK wordV
  have key : ∀ (w : List ℕ) (acc : ℕ), List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
      (fun a _ ih acc => letN (cmulK acc (letterK (packL BL) g a)) ih) w acc =
      w.foldl (fun acc a => Code.mul acc (letterV BL g a)) acc := by
    intro w
    induction w with
    | nil => intro acc; rfl
    | cons a t ih =>
      intro acc
      change letN (cmulK acc (letterK (packL BL) g a)) _ = _
      rw [letN_gl, ih, List.foldl_cons, cmulK_eq, letterK_gl hBL]
  exact key w ONE

theorem rep_gl (GD : List (ℕ × List ℕ)) (a : ℕ) : nthK (fstK GD) 0 a = rep GD a := by
  rw [nthK_gl, fstK_gl, rep, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases GD[a]? <;> rfl

theorem orb_gl (GD : List (ℕ × List ℕ)) (b : ℕ) :
    Prod.rec (motive := fun _ => List ℕ) (fun _ O => O) (nthK GD (0, List.nil) b) = orbL GD b := by
  rw [nthK_gl]
  rfl

theorem orb2_gl (GD : List (ℕ × List ℕ)) (b : ℕ) : (nthK GD (0, List.nil) b).2 = orbL GD b := by
  rw [nthK_gl]
  rfl

theorem bK_basic {BL BIL : List ℕ} {BP BIP : ℕ} {BT : List (ℕ × ℕ × ℕ)}
    (h : bK BL BIL BP BIP BT = true) : (∀ x ∈ BL, x < 2 ^ 36) ∧ BP = packL BL := by
  unfold bK at h
  simp only [andB_gl, Bool.and_eq_true, beq_gl] at h
  obtain ⟨h1, -, -, -, -, h2, -⟩ := h
  exact ⟨fun x hx => ((incK_gl 0 BL h1).1 x hx).2, h2⟩

theorem lt64 {BL : List ℕ} (h : ∀ x ∈ BL, x < 2 ^ 36) : ∀ x ∈ BL, x < 2 ^ 64 :=
  fun x hx => lt_of_lt_of_le (h x hx) (Nat.pow_le_pow_right (by norm_num) (by norm_num))

theorem bK_facts {BL BIL : List ℕ} {BP BIP : ℕ} {BT : List (ℕ × ℕ × ℕ)}
    (h : bK BL BIL BP BIP BT = true) : BL.length = 336 ∧ BIL.length = 336 ∧
      (∀ x ∈ BIL, x < 2 ^ 36) ∧ BIP = packL BIL := by
  unfold bK at h
  simp only [andB_gl, Bool.and_eq_true, beq_gl, lenN_gl, allL_gl, List.all_eq_true, blt_gl,
    T36_eq] at h
  obtain ⟨-, h1, -, h2, h3, -, h4, -⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem getD_eq {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_lt {l : List ℕ} (h : ∀ x ∈ l, x < 2 ^ 36) (t : ℕ) : l.getD t 0 < 2 ^ 36 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hq : l[t]? with _ | x
  · simp
  · exact h x (List.mem_of_getElem? hq)

open CFSG.KC.GL62.LS in
theorem packL336 {l : List ℕ} (h1 : l.length = 336) (h2 : ∀ x ∈ l, x < 2 ^ 36) :
    packL l = ofF 336 fun t => l.getD t 0 := by
  rw [packL_eq_ofF (lt64 h2), h1]

open CFSG.KC.GL62.LS in
theorem mulLrep_gl (c N : ℕ) : Nat.mul c (lrep N) = ofF N fun _ => c := const_mul_lrep c N

open CFSG.KC.GL62.LS in
theorem laneProd {N : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < N, f t < 2 ^ 36) (hg : ∀ t < N, g t < 2 ^ 36) :
    mulL (Nat.mul R6 (lrep N)) (Nat.mul 63 (lrep N)) (ofF N f) (ofF N g) =
      ofF N fun t => Code.mul (g t) (f t) := by
  rw [mulLrep_gl, mulLrep_gl, mulL_ofF hf hg]
  exact ofF_congr fun t _ => cmulK_eq (g t) (f t)

open CFSG.KC.GL62.LS in
theorem conjL_gl {BL BIL : List ℕ} (h1 : BL.length = 336) (h2 : ∀ x ∈ BL, x < 2 ^ 36)
    (h3 : BIL.length = 336) (h4 : ∀ x ∈ BIL, x < 2 ^ 36) {r : ℕ} (hr : r < 2 ^ 36) :
    conjL (lrep 336) (Nat.mul R6 (lrep 336)) (Nat.mul 63 (lrep 336)) (packL BL) (packL BIL) r =
      ofF 336 fun k => conjB BL BIL k r := by
  unfold conjL
  rw [mulLrep_gl r, packL336 h1 h2, packL336 h3 h4,
    laneProd (fun _ _ => hr) (fun t _ => getD_lt h2 t),
    laneProd (fun t _ => getD_lt h4 t) (fun t _ => Code.mul_lt _ _)]
  rfl

theorem xor_zero_gl {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have : a ^^^ b ^^^ b = b := by rw [h, Nat.zero_xor]
  rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this

theorem count_gl (N : ℕ) (c : ℕ → ℕ) (r : ℕ) :
    ((List.range N).filter fun k => c k = r).length +
      ∑ i ∈ Finset.range N, (if c i ^^^ r = 0 then 0 else 1) = N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, Finset.sum_range_succ]
    by_cases h : c N = r
    · simp [h]
      omega
    · have : c N ^^^ r ≠ 0 := fun h0 => h (xor_zero_gl h0)
      simp [h, this]
      omega

theorem count2_gl (N : ℕ) (c d : ℕ → ℕ) :
    ((List.range N).filter fun k => c k = d k).length +
      ∑ i ∈ Finset.range N, (if c i ^^^ d i = 0 then 0 else 1) = N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, Finset.sum_range_succ]
    by_cases h : c N = d N
    · simp [h]
      omega
    · have : c N ^^^ d N ≠ 0 := fun h0 => h (xor_zero_gl h0)
      simp [h, this]
      omega

theorem filter_range_gl (l : List ℕ) (p : ℕ → Bool) :
    ((List.range l.length).filter fun k => p (l.getD k 0)).length = (l.filter p).length := by
  have hmap : (List.range l.length).map (fun k => l.getD k 0) = l :=
    List.ext_getElem (by simp) fun i h1 h2 => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  conv_rhs => rw [← hmap]
  rw [List.countP_map]
  rfl

open CFSG.KC.GL62.LS in
theorem xorF_gl {N : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < N, f t < 2 ^ 64) (hg : ∀ t < N, g t < 2 ^ 64) :
    Nat.xor (ofF N f) (ofF N g) = ofF N fun t => f t ^^^ g t := ofF_xor hf hg

theorem witC_gl (BP : ℕ) (W : List (ℕ × ℕ)) :
    witC BP W = packL (W.map fun x => laneK BP x.2) := by
  induction W with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨p, k⟩ := x
    change Nat.lor (laneK BP k) (Nat.shiftLeft (witC BP t) 64) =
      Nat.lor (laneK BP k) (Nat.shiftLeft (packL (t.map fun x => laneK BP x.2)) 64)
    rw [ih]

theorem witR_gl (RP : ℕ) (W : List (ℕ × ℕ)) :
    witR RP W = packL (W.map fun x => laneK RP x.1) := by
  induction W with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨p, k⟩ := x
    change Nat.lor (laneK RP p) (Nat.shiftLeft (witR RP t) 64) =
      Nat.lor (laneK RP p) (Nat.shiftLeft (packL (t.map fun x => laneK RP x.1)) 64)
    rw [ih]

theorem witOK_gl {W : List (ℕ × ℕ)} (h : witOK W = true) : ∀ x ∈ W, x.1 < 17 ∧ x.2 < 336 := by
  unfold witOK at h
  rw [allK_gl, List.all_eq_true] at h
  intro x hx
  have := h x hx
  obtain ⟨p, k⟩ := x
  simp only [andB_gl, Bool.and_eq_true, blt_gl] at this
  exact this

theorem getD_map_lt {α : Type} (l : List α) (f : α → ℕ) (d : α) (t : ℕ) (ht : t < l.length) :
    (l.map f).getD t 0 = f (l.getD t d) := by
  rw [getD_eq _ _ t (by simpa using ht), getD_eq _ _ t ht, List.getElem_map]

open CFSG.KC.GL62.LS in
theorem goodPair_gl {BL : List ℕ} (hlt : ∀ x ∈ BL, x < 2 ^ 36) {GD : List (ℕ × List ℕ)}
    (hRP : ∀ x ∈ fstK GD, x < 2 ^ 36) {ra : ℕ} (hra : ra < 2 ^ 36) {O : List ℕ}
    (hO : ∀ x ∈ O, x < 2 ^ 36) {h : ℕ} {W : List (ℕ × ℕ)}
    (hgp : goodPair (packL BL) (packL (fstK GD)) ra O h W = true) :
    W.length = O.length ∧ (∀ x ∈ W, x.1 < 17 ∧ x.2 < 336) ∧ h = bitsK (W.map Prod.fst) ∧
      ∀ t < O.length, Code.mul (BL.getD (W.getD t (0, 0)).2 0) (rep GD (W.getD t (0, 0)).1) =
        Code.mul (Code.mul (Code.mul ra (O.getD t 0)) ra) (BL.getD (W.getD t (0, 0)).2 0) := by
  unfold goodPair at hgp
  simp only [letB_gl, andB_gl, Bool.and_eq_true, blt_gl, beq_gl, lenN_gl, lenK_gl] at hgp
  obtain ⟨hN, hWl, hok, hh, hlane⟩ := hgp
  refine ⟨hWl, witOK_gl hok, by rw [hh, witM, fstK_gl], fun t ht => ?_⟩
  have hBL : ∀ k, laneK (packL BL) k = BL.getD k 0 := laneK_packL (lt64 hlt)
  have hR : ∀ p, laneK (packL (fstK GD)) p = rep GD p := fun p => by
    rw [laneK_packL (lt64 hRP), ← nthK_gl, rep_gl]
  have hRl : ∀ p, rep GD p < 2 ^ 36 := fun p => by
    rw [← hR, laneK_packL (lt64 hRP)]
    exact getD_lt hRP p
  have hCb : ∀ x ∈ W.map (fun x => laneK (packL BL) x.2), x < 2 ^ 36 := fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    rw [hBL]
    exact getD_lt hlt _
  have hRb : ∀ x ∈ W.map (fun x => laneK (packL (fstK GD)) x.1), x < 2 ^ 36 := fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    rw [hR]
    exact hRl _
  rw [witC_gl, witR_gl, packL_eq_ofF (lt64 hCb), packL_eq_ofF (lt64 hRb), packL_eq_ofF (lt64 hO),
    List.length_map, List.length_map, hWl, mulLrep_gl ra] at hlane
  have hOl : ∀ t < O.length, O.getD t 0 < 2 ^ 36 := fun t _ => getD_lt hO t
  rw [laneProd (f := fun t => O.getD t 0) (g := fun _ => ra) hOl (fun _ _ => hra),
    laneProd (f := fun _ => ra) (g := fun t => Code.mul ra (O.getD t 0)) (fun _ _ => hra)
      (fun _ _ => Code.mul_lt _ _),
    laneProd (f := fun t => (W.map fun x => laneK (packL (fstK GD)) x.1).getD t 0)
      (g := fun t => (W.map fun x => laneK (packL BL) x.2).getD t 0)
      (fun t _ => getD_lt hRb t) (fun t _ => getD_lt hCb t),
    laneProd (f := fun t => (W.map fun x => laneK (packL BL) x.2).getD t 0)
      (g := fun t => Code.mul (Code.mul ra (O.getD t 0)) ra)
      (fun t _ => getD_lt hCb t) (fun _ _ => Code.mul_lt _ _)] at hlane
  have := ofF_inj (fun t _ => lt_of_lt_of_le (Code.mul_lt _ _) two36_le)
    (fun t _ => lt_of_lt_of_le (Code.mul_lt _ _) two36_le) hlane t ht
  have htW : t < W.length := by omega
  rw [getD_map_lt W _ (0, 0) t htW, getD_map_lt W _ (0, 0) t htW, hBL, hR] at this
  exact this

theorem exists_zero_gl {N : ℕ} {f : ℕ → ℕ}
    (h : ∑ i ∈ Finset.range N, (if f i = 0 then 0 else 1) < N) : ∃ i < N, f i = 0 := by
  by_contra hne
  have hne' : ∀ i < N, f i ≠ 0 := fun i hi h0 => hne ⟨i, hi, h0⟩
  have : ∑ i ∈ Finset.range N, (if f i = 0 then 0 else 1) = N := by
    rw [Finset.sum_congr rfl fun i hi => if_neg (hne' i (Finset.mem_range.1 hi))]
    simp
  omega

open CFSG.KC.GL62.LS in
theorem nzX_gl {c : ℕ → ℕ} (hc : ∀ t < 336, c t < 2 ^ 36) {x : ℕ} (hx : x < 2 ^ 36) :
    nzL 336 (lrep 336) (Nat.xor (ofF 336 c) (Nat.mul x (lrep 336))) =
      ∑ i ∈ Finset.range 336, if c i ^^^ x = 0 then 0 else 1 := by
  have h64 : ∀ t < 336, c t < 2 ^ 64 := fun t ht => lt_of_lt_of_le (hc t ht)
    (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hx64 : ∀ t < 336, (fun _ => x) t < 2 ^ 64 := fun _ _ => lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  rw [mulLrep_gl]
  change nzL 336 (lrep 336) (ofF 336 c ^^^ ofF 336 fun _ => x) = _
  rw [ofF_xor h64 hx64, nzL_ofF (by norm_num) (by norm_num)
    (fun t ht => Nat.xor_lt_two_pow (hc t ht) hx)]

theorem stabK_gl {c : ℕ → ℕ} (hc : ∀ t < 336, c t < 2 ^ 36) {r : ℕ} (hr : r < 2 ^ 36) :
    stabK (lrep 336) (CFSG.KC.GL62.LS.ofF 336 c) r =
      ((List.range 336).filter fun k => c k = r).length := by
  unfold stabK
  change 336 - nzL 336 (lrep 336) (Nat.xor (CFSG.KC.GL62.LS.ofF 336 c) (Nat.mul r (lrep 336))) = _
  rw [nzX_gl hc hr]
  have := count_gl 336 c r
  omega

theorem z0_sq : Code.mul 38959071361 38959071361 = Code.one := by decide

theorem inv_gl {g g' r : ℕ} (h2 : Code.mul g g' = Code.one) (h3 : Code.mul g' g = Code.one)
    (h : Code.mul (Code.mul g 38959071361) g' = r) : Code.mul r r = Code.one := by
  subst h
  apply Code.eq_of_mat_eq (Code.mul_lt _ _) Code.one_lt
  have a := Code.mat_mul_eq_one h2
  have b := Code.mat_mul_eq_one h3
  have c := Code.mat_mul_eq_one z0_sq
  simp only [Code.mat_mul, Code.mat_one]
  have e : ∀ A B C : Matrix (Fin 6) (Fin 6) (ZMod 2),
      (A * B * C) * (A * B * C) = A * B * (C * A) * B * C := by
    intro A B C
    simp only [Matrix.mul_assoc]
  rw [e, b, Matrix.mul_one, Matrix.mul_assoc (Code.mat g), c, Matrix.mul_one, a]

open CFSG.KC.GL62.LS in
theorem badW_gl {BL : List ℕ} (hBL : ∀ x ∈ BL, x < 2 ^ 64) {y : ℕ} {w : List ℕ}
    (h : badW (packL BL) y w = true) : BadW BL y w := by
  unfold badW at h
  rw [andB_gl, letB_gl, Bool.and_eq_true, andB_gl, Bool.and_eq_true, notB_gl, beq_gl,
    Bool.not_eq_true', cmulK_eq, cmulK_eq, wordK_gl hBL] at h
  exact ⟨lettersK_gl h.1, h.2.1, h.2.2⟩

noncomputable def ordF : List (ℕ × ℕ × ℕ × ℕ × List ℕ) → ℕ → ℕ → ℕ → Bool := fun l =>
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → Bool)
    (fun _ sum cnt => andB (Nat.beq sum 234360) (Nat.beq cnt 827))
    (fun x _ ih prev sum cnt => Prod.rec (motive := fun _ => Bool) (fun r rest =>
      Prod.rec (motive := fun _ => Bool) (fun s _ => andB (Nat.blt prev r)
        (letB (Nat.add sum (Nat.div 336 s)) fun sum' => letB (Nat.succ cnt) fun cnt' =>
          ih r sum' cnt')) rest) x) l

theorem ordF_true : ∀ (l : List (ℕ × ℕ × ℕ × ℕ × List ℕ)) (prev sum cnt : ℕ),
    ordF l prev sum cnt = true → (∀ x ∈ l, prev < x.1) ∧ (l.map Prod.fst).Pairwise (· < ·) ∧
      sum + (l.map fun x => 336 / x.2.1).sum = 234360 ∧ cnt + l.length = 827 := by
  intro l
  induction l with
  | nil =>
    intro prev sum cnt h
    change andB (Nat.beq sum 234360) (Nat.beq cnt 827) = true at h
    rw [andB_gl, Bool.and_eq_true, beq_gl, beq_gl] at h
    simp [h.1, h.2]
  | cons x t ih =>
    intro prev sum cnt h
    obtain ⟨r, s, rest⟩ := x
    change andB (Nat.blt prev r) (letB (Nat.add sum (Nat.div 336 s)) fun sum' =>
      letB (Nat.succ cnt) fun cnt' => ordF t r sum' cnt') = true at h
    rw [andB_gl, Bool.and_eq_true, blt_gl, letB_gl, letB_gl] at h
    obtain ⟨h1, h2, h3, h4⟩ := ih _ _ _ h.2
    refine ⟨fun y hy => ?_, ?_, ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact h.1
      · exact h.1.trans (h1 y hy)
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun b hb => ?_, h2⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      exact h1 y hy
    · rw [List.map_cons, List.sum_cons, ← Nat.add_assoc]
      exact h3
    · rw [List.length_cons]
      change cnt + 1 + t.length = 827 at h4
      omega

variable {BL BIL : List ℕ} {BP BIP : ℕ} {RC : List (List (ℕ × ℕ × ℕ × ℕ × List ℕ))}
  {GD : List (ℕ × List ℕ)} {C H : List (List ℕ)} {HW : List (List (List (ℕ × ℕ)))}
  {HB : List (ℕ × ℕ × ℕ × List ℕ)} {F : List (ℕ × ℕ × ℕ × List (ℕ × List ℕ))}
  {BT : List (ℕ × ℕ × ℕ)}

@[expose] def parT (BT : List (ℕ × ℕ × ℕ)) (k : ℕ) : ℕ := (BT.getD k (0, 0, 0)).1

@[expose] def letT (BT : List (ℕ × ℕ × ℕ)) (k : ℕ) : ℕ := (BT.getD k (0, 0, 0)).2.1

@[expose] def depT (BT : List (ℕ × ℕ × ℕ)) (k : ℕ) : ℕ := (BT.getD k (0, 0, 0)).2.2

theorem bK_sound (h : bK BL BIL BP BIP BT = true) :
    BL.length = 336 ∧ BL.Pairwise (· < ·) ∧ (∀ x ∈ BL, x < 2 ^ 36) ∧ (∀ x ∈ BL, blkK x = true) ∧
      BIL.length = 336 ∧ (∀ x ∈ BIL, x < 2 ^ 36) ∧ BP = packL BL ∧ BIP = packL BIL ∧
      (∀ k < 336, Code.mul (BL.getD k 0) (BIL.getD k 0) = Code.one ∧
        Code.mul (BIL.getD k 0) (BL.getD k 0) = Code.one) ∧
      ∀ k < 336, letT BT k ≤ 2 ∧ ((depT BT k = 0 ∧ BL.getD k 0 = Code.one) ∨
        (depT BT k ≠ 0 ∧ parT BT k < 336 ∧ depT BT (parT BT k) + 1 = depT BT k ∧
          Code.mul (BL.getD (parT BT k) 0) (genK (letT BT k)) = BL.getD k 0)) := by
  unfold bK at h
  simp only [andB_gl, Bool.and_eq_true, beq_gl, lenN_gl, allL_gl, List.all_eq_true, blt_gl,
    T36_eq, letB_gl] at h
  obtain ⟨hinc, hl1, hblk, hl2, hlt2, rfl, rfl, hm1, hm2, htree⟩ := h
  obtain ⟨hlt0, hpw⟩ := incK_gl 0 BL hinc
  have hlt : ∀ x ∈ BL, x < 2 ^ 36 := fun x hx => (hlt0 x hx).2
  have hone : ∀ t < 336, (fun _ => ONE) t < 2 ^ 64 := fun _ _ => by norm_num [ONE]
  have hm : ∀ t < 336, (fun t => Code.mul (BIL.getD t 0) (BL.getD t 0)) t < 2 ^ 64 :=
    fun t _ => lt_of_lt_of_le (Code.mul_lt _ _) CFSG.KC.GL62.LS.two36_le
  have hm' : ∀ t < 336, (fun t => Code.mul (BL.getD t 0) (BIL.getD t 0)) t < 2 ^ 64 :=
    fun t _ => lt_of_lt_of_le (Code.mul_lt _ _) CFSG.KC.GL62.LS.two36_le
  rw [packL336 hl1 hlt, packL336 hl2 hlt2, laneProd (fun t _ => getD_lt hlt t)
    (fun t _ => getD_lt hlt2 t), mulLrep_gl] at hm1
  rw [packL336 hl1 hlt, packL336 hl2 hlt2, laneProd (fun t _ => getD_lt hlt2 t)
    (fun t _ => getD_lt hlt t), mulLrep_gl] at hm2
  have i1 := CFSG.KC.GL62.LS.ofF_inj hm hone hm1
  have i2 := CFSG.KC.GL62.LS.ofF_inj hm' hone hm2
  unfold treeK at htree
  rw [letB_gl] at htree
  obtain ⟨hlenT, hz⟩ := zipK_gl _ BL BT 0 htree
  have key : ∀ k < 336, letT BT k ≤ 2 ∧ depT BT k < 336 ∧
      ((depT BT k = 0 ∧ BL.getD k 0 = Code.one) ∨ (depT BT k ≠ 0 ∧ parT BT k < 336 ∧
        laneK (packL (depthsK BT)) (parT BT k) + 1 = depT BT k ∧
        Code.mul (laneK (packL BL) (parT BT k)) (genK (letT BT k)) = BL.getD k 0)) := by
    intro k hk
    have hk1 : k < BL.length := by omega
    have hk2 : k < BT.length := by omega
    have := hz k hk1 hk2
    unfold parT letT depT
    rw [getD_eq BT _ k hk2, getD_eq BL _ k hk1]
    generalize BT[k] = e at this
    obtain ⟨par, l, d⟩ := e
    simp only [andB_gl, Bool.and_eq_true, ble_gl, blt_gl] at this
    obtain ⟨hl, hd, hrest⟩ := this
    refine ⟨hl, hd, ?_⟩
    by_cases hd0 : d = 0
    · subst hd0
      have h1 : Nat.beq BL[k] ONE = true := hrest
      exact Or.inl ⟨rfl, beq_gl.1 h1⟩
    · have hb : Nat.beq d 0 = false := by
        rcases hq : Nat.beq d 0 with _ | _
        · rfl
        · exact absurd (beq_gl.1 hq) hd0
      rw [hb] at hrest
      simp only [andB_gl, Bool.and_eq_true, blt_gl, beq_gl] at hrest
      obtain ⟨h1, h2, h3⟩ := hrest
      rw [CFSG.KC.GL62.LS.cmulK_eq] at h3
      exact Or.inr ⟨hd0, h1, h2, h3⟩
  have hd64 : ∀ x ∈ depthsK BT, x < 2 ^ 64 := by
    rw [depthsK_gl]
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have := (key i (by omega)).2.1
    unfold depT at this
    rw [getD_eq BT _ i hi] at this
    exact lt_of_lt_of_le this (by norm_num)
  have hdep : ∀ p, laneK (packL (depthsK BT)) p = depT BT p := by
    intro p
    rw [CFSG.KC.GL62.LS.laneK_packL hd64, depthsK_gl, depT, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_map]
    cases BT[p]? <;> rfl
  refine ⟨hl1, hpw, hlt, hblk, hl2, hlt2, rfl, rfl, fun k hk => ⟨(i2 k hk), (i1 k hk)⟩,
    fun k hk => ?_⟩
  obtain ⟨h1, -, h3⟩ := key k hk
  rcases h3 with h3 | ⟨h3, h4, h5, h6⟩
  · exact ⟨h1, Or.inl h3⟩
  · rw [hdep] at h5
    rw [CFSG.KC.GL62.LS.laneK_packL (lt64 hlt)] at h6
    exact ⟨h1, Or.inr ⟨h3, h4, h5, h6⟩⟩

theorem rc_sound (hb : bK BL BIL BP BIP BT = true) (hlen : Nat.beq (lenK RC) 13 = true)
    (hrc : ∀ j < 13, rcK BP BIP (headsK GD) (nthK RC [] j) = true) :
    ∀ x ∈ RC.flatten, x.1 < 2 ^ 36 ∧ Code.mul x.1 x.1 = Code.one ∧
      (∀ k < 336, x.1 ≤ conjB BL BIL k x.1) ∧ x.2.1 = stabB BL BIL x.1 ∧ 0 < x.2.1 ∧
      x.2.1 ∣ 336 ∧ Code.mul (Code.mul x.2.2.1 38959071361) x.2.2.2.1 = x.1 ∧
      Code.mul x.2.2.1 x.2.2.2.1 = Code.one ∧ Code.mul x.2.2.2.1 x.2.2.1 = Code.one ∧
      (x.1 ∉ GD.map (fun e => e.2.getD 0 0) → BadW BL x.1 x.2.2.2.2) := by
  obtain ⟨hlt, rfl⟩ := bK_basic hb
  obtain ⟨hl1, hl2, hlt2, rfl⟩ := bK_facts hb
  intro x hx
  obtain ⟨ch, hch, hxc⟩ := List.mem_flatten.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hch
  have hl : RC.length = 13 := by
    rw [← lenK_gl]
    exact beq_gl.1 hlen
  have hc := hrc j (by omega)
  rw [nthK_gl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hc
  unfold rcK at hc
  simp only [letB_gl, allK_gl, List.all_eq_true] at hc
  have hrec := hc _ hxc
  obtain ⟨r, s, g, g', w⟩ := x
  unfold recK at hrec
  simp only [andB_gl, Bool.and_eq_true, blt_gl, letB_gl, beq_gl, T36_eq] at hrec
  obtain ⟨hr, hs, hge, hs0, hmod, hg1, hg2, hg3, hbw⟩ := hrec
  rw [conjL_gl hl1 hlt hl2 hlt2 hr] at hs hge
  rw [stabK_gl (c := fun k => conjB BL BIL k r) (fun t _ => Code.mul_lt _ _) hr] at hs
  have hge' := CFSG.KC.GL62.LS.geL_ofF hr (fun t _ => Code.mul_lt _ _) hge
  rw [CFSG.KC.GL62.LS.cmulK_eq, CFSG.KC.GL62.LS.cmulK_eq] at hg1
  rw [CFSG.KC.GL62.LS.cmulK_eq] at hg2 hg3
  have hbad : r ∉ GD.map (fun e => e.2.getD 0 0) → BadW BL r w := by
    intro hnot
    cases hn : nilK w with
    | true =>
      rw [hn] at hbw
      exact absurd ((memN_gl _ _).1 hbw) (by rwa [headsK_gl])
    | false =>
      rw [hn] at hbw
      exact badW_gl (lt64 hlt) hbw
  exact ⟨hr, inv_gl hg2 hg3 hg1, hge', hs.symm, hs0, Nat.dvd_of_mod_eq_zero hmod, hg1, hg2, hg3,
    hbad⟩

theorem ordK_sound (h : ordK RC = true) :
    (RC.flatten.map Prod.fst).Pairwise (· < ·) ∧ RC.flatten.length = 827 ∧
      (RC.flatten.map fun x => 336 / x.2.1).sum = 234360 := by
  have := ordF_true (flatK RC) 0 0 0 h
  rw [flatK_gl] at this
  obtain ⟨-, h2, h3, h4⟩ := this
  exact ⟨h2, by omega, by omega⟩

theorem goodK_sound (h : goodK BP BIP GD = true) (hb : bK BL BIL BP BIP BT = true) :
    GD.length = 17 ∧ rep GD 0 = 38959071361 ∧ (GD.map fun e => e.2.getD 0 0).Nodup ∧
      ∀ p < 17, rep GD p < 2 ^ 36 ∧ Code.mul (rep GD p) (rep GD p) = Code.one ∧
        0 < stabB BL BIL (rep GD p) ∧ (orbL GD p).Pairwise (· < ·) ∧
        (orbL GD p).length = 336 / stabB BL BIL (rep GD p) ∧
        ∀ x ∈ orbL GD p, ∃ k < 336, conjB BL BIL k (rep GD p) = x := by
  obtain ⟨hlt, rfl⟩ := bK_basic hb
  obtain ⟨hl1, hl2, hlt2, rfl⟩ := bK_facts hb
  unfold goodK at h
  simp only [andB_gl, Bool.and_eq_true, beq_gl, letB_gl, allK_gl, List.all_eq_true, nodupN_gl,
    lenK_gl, rep_gl, headsK_gl] at h
  obtain ⟨hlen, h0, hnd, hall⟩ := h
  refine ⟨hlen, h0, hnd, fun p hp => ?_⟩
  have hp' : p < GD.length := by omega
  have hrep : rep GD p = (GD[p]).1 ∧ orbL GD p = (GD[p]).2 := by
    constructor <;> simp [rep, orbL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp']
  have he := hall _ (List.getElem_mem hp')
  rw [hrep.1, hrep.2]
  generalize GD[p] = e at he
  obtain ⟨r, O⟩ := e
  simp only [andB_gl, Bool.and_eq_true, blt_gl, letB_gl, beq_gl, T36_eq, lenN_gl, allL_gl,
    List.all_eq_true] at he
  obtain ⟨hr, hrr, hs0, hinc, hlenO, hmem⟩ := he
  rw [conjL_gl hl1 hlt hl2 hlt2 hr] at hs0 hlenO hmem
  rw [stabK_gl (c := fun k => conjB BL BIL k r) (fun t _ => Code.mul_lt _ _) hr] at hs0 hlenO
  rw [CFSG.KC.GL62.LS.cmulK_eq] at hrr
  obtain ⟨hO1, hO2⟩ := incK_gl 0 O hinc
  refine ⟨hr, hrr, hs0, hO2, hlenO, fun x hx => ?_⟩
  have := hmem x hx
  rw [nzX_gl (c := fun k => conjB BL BIL k r) (fun t _ => Code.mul_lt _ _) (hO1 x hx).2] at this
  obtain ⟨k, hk, hk0⟩ := exists_zero_gl this
  exact ⟨k, hk, xor_zero_gl hk0⟩

theorem commK_sound (hc : commK GD C = true) (hg : goodK BP BIP GD = true)
    (hb : bK BL BIL BP BIP BT = true) :
    ∀ a < GD.length, ∀ b < GD.length, tab C a b =
      ((orbL GD b).filter fun x => Code.mul x (rep GD a) = Code.mul (rep GD a) x).length := by
  obtain ⟨hlen, -, -, hp⟩ := goodK_sound hg hb
  unfold commK at hc
  obtain ⟨hl, hz⟩ := zipK_gl _ GD C 0 hc
  intro a ha b hb'
  have h1 := hz a ha (by omega)
  have hrep : rep GD a = GD[a].1 := by
    unfold rep
    rw [getD_eq GD _ a ha]
  have horb : orbL GD b = GD[b].2 := by
    unfold orbL
    rw [getD_eq GD _ b hb']
  change commRow GD GD[a].1 C[a] = true at h1
  unfold commRow at h1
  obtain ⟨hl2, hz2⟩ := zipK_gl _ GD C[a] 0 h1
  have h2 := hz2 b hb' (by omega)
  have hcb : tab C a b = C[a][b] := by
    unfold tab
    rw [getD_eq C _ a (by omega), getD_eq _ 0 b (by omega)]
  obtain ⟨hra, -, -, -, -, -⟩ := hp a (by omega)
  obtain ⟨-, -, -, -, hlenO, hmemO⟩ := hp b (by omega)
  have hOb : ∀ x ∈ GD[b].2, x < 2 ^ 36 := fun x hx => by
    rw [← horb] at hx
    obtain ⟨k, -, rfl⟩ := hmemO x hx
    exact Code.mul_lt _ _
  have hNle : GD[b].2.length ≤ 336 := by
    rw [← horb, hlenO]
    exact Nat.div_le_self _ _
  rw [hcb, hrep, horb]
  rw [hrep] at hra
  generalize GD[b] = e at h2 hOb hNle ⊢
  obtain ⟨r', O⟩ := e
  change O.length ≤ 336 at hNle
  change ∀ x ∈ O, x < 2 ^ 36 at hOb
  simp only [letB_gl, andB_gl, Bool.and_eq_true, blt_gl, beq_gl, lenN_gl] at h2
  obtain ⟨hN, hcnt⟩ := h2
  rw [← hcnt]
  have hO : ∀ t < O.length, O.getD t 0 < 2 ^ 36 := fun t _ => getD_lt hOb t
  rw [CFSG.KC.GL62.LS.packL_eq_ofF (lt64 hOb), mulLrep_gl GD[a].1,
    laneProd (fun _ _ => hra) hO, laneProd hO (fun _ _ => hra),
    xorF_gl (fun t _ => lt_of_lt_of_le (Code.mul_lt _ _) CFSG.KC.GL62.LS.two36_le)
      (fun t _ => lt_of_lt_of_le (Code.mul_lt _ _) CFSG.KC.GL62.LS.two36_le),
    CFSG.KC.GL62.LS.nzL_ofF hN (by omega)
      (fun t _ => Nat.xor_lt_two_pow (Code.mul_lt _ _) (Code.mul_lt _ _)),
    ← filter_range_gl O (fun x => decide (Code.mul x GD[a].1 = Code.mul GD[a].1 x))]
  have := count2_gl O.length (fun t => Code.mul (O.getD t 0) GD[a].1)
    (fun t => Code.mul GD[a].1 (O.getD t 0))
  change O.length - _ = _
  omega

theorem hitK_sound (hb : bK BL BIL BP BIP BT = true) (hg : goodK BP BIP GD = true)
    (hh : ∀ a < 17, hitK BP GD HB H HW a = true) :
    ∀ a < 17, ∀ b < 17,
      (tab H a b = 2 ^ 17 → ∃ e ∈ HB, e.1 = a ∧ e.2.1 = b) ∧
      (tab H a b ≠ 2 ^ 17 →
        (∀ x ∈ orbL GD b, ∃ n < 17, (tab H a b).testBit n = true ∧ ∃ k < 336,
          Code.mul (BL.getD k 0) (rep GD n) =
            Code.mul (Code.mul (Code.mul (rep GD a) x) (rep GD a)) (BL.getD k 0)) ∧
        ∀ n, (tab H a b).testBit n = true → n < 17 ∧ ∃ x ∈ orbL GD b, ∃ k < 336,
          Code.mul (BL.getD k 0) (rep GD n) =
            Code.mul (Code.mul (Code.mul (rep GD a) x) (rep GD a)) (BL.getD k 0)) := by
  obtain ⟨hlt, rfl⟩ := bK_basic hb
  obtain ⟨hlen, -, -, hp⟩ := goodK_sound hg hb
  have hRP : ∀ x ∈ fstK GD, x < 2 ^ 36 := by
    rw [fstK_gl]
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have := (hp i (by omega)).1
    unfold rep at this
    rwa [getD_eq _ _ i hi] at this
  intro a ha b hb'
  have h1 := hh a ha
  unfold hitK at h1
  simp only [andB_gl, Bool.and_eq_true, blt_gl, letB_gl, rep_gl] at h1
  obtain ⟨-, h1⟩ := h1
  unfold hitRow at h1
  simp only [andB_gl, Bool.and_eq_true, beq_gl, lenK_gl] at h1
  obtain ⟨-, hz⟩ := h1
  obtain ⟨hWl, hz⟩ := zipK_gl _ GD _ 0 hz
  have h2 := hz b (by omega) (by omega)
  generalize (nthK HW [] a)[b]'(by omega) = W at h2
  simp only [letB_gl, nthK_gl, Nat.zero_add] at h2
  have htab : (H.getD a []).getD b 0 = tab H a b := rfl
  rw [htab] at h2
  have horb : orbL GD b = GD[b].2 := by
    unfold orbL
    rw [getD_eq GD _ b (by omega)]
  obtain ⟨-, -, -, -, -, hmemO⟩ := hp b hb'
  have hOb : ∀ x ∈ GD[b].2, x < 2 ^ 36 := fun x hx => by
    rw [← horb] at hx
    obtain ⟨k, -, rfl⟩ := hmemO x hx
    exact Code.mul_lt _ _
  have hra := (hp a ha).1
  rw [horb]
  generalize GD[b] = e at h2 hOb ⊢
  obtain ⟨r', O⟩ := e
  change ∀ x ∈ O, x < 2 ^ 36 at hOb
  change Bool.rec (motive := fun _ => Bool) (goodPair (packL BL) (packL (fstK GD)) (rep GD a) O
    (tab H a b) W) (hbHas HB a b) (Nat.beq (tab H a b) 131072) = true at h2
  by_cases hT : tab H a b = 2 ^ 17
  · have hq : Nat.beq (tab H a b) 131072 = true := beq_gl.2 (by rw [hT]; norm_num)
    rw [hq] at h2
    refine ⟨fun _ => ?_, fun hne => absurd hT hne⟩
    change hbHas HB a b = true at h2
    unfold hbHas at h2
    rw [anyK_gl, List.any_eq_true] at h2
    obtain ⟨e, he, hm⟩ := h2
    obtain ⟨a', b', rest⟩ := e
    simp only [andB_gl, Bool.and_eq_true, beq_gl] at hm
    exact ⟨_, he, hm.1.symm, hm.2.symm⟩
  · have hq : Nat.beq (tab H a b) 131072 = false := by
      rcases hq : Nat.beq (tab H a b) 131072 with _ | _
      · rfl
      · exact absurd ((beq_gl.1 hq).trans (by norm_num)) hT
    rw [hq] at h2
    obtain ⟨hWO, hok, hbits, hlane⟩ := goodPair_gl hlt hRP hra hOb h2
    refine ⟨fun h => absurd h hT, fun _ => ⟨fun x hx => ?_, fun n hn => ?_⟩⟩
    · change x ∈ O at hx
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
      have htW : t < W.length := by omega
      have hw := hok (W[t]) (List.getElem_mem htW)
      refine ⟨W[t].1, hw.1, ?_, W[t].2, hw.2, ?_⟩
      · rw [hbits, bitsK_gl]
        exact List.mem_map.2 ⟨W[t], List.getElem_mem htW, rfl⟩
      · have := hlane t ht
        rw [getD_eq W _ t htW, getD_eq O _ t ht] at this
        exact this
    · rw [hbits, bitsK_gl, List.mem_map] at hn
      obtain ⟨w, hw, rfl⟩ := hn
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hw
      have htO : t < O.length := by omega
      have hw' := hok _ hw
      refine ⟨hw'.1, O[t], List.getElem_mem htO, W[t].2, hw'.2, ?_⟩
      have := hlane t htO
      rw [getD_eq W _ t ht, getD_eq O _ t htO] at this
      exact this

theorem hbK_sound (hbb : hbK BP GD HB = true) (hb : bK BL BIL BP BIP BT = true) :
    ∀ e ∈ HB, e.1 < 17 ∧ e.2.1 < 17 ∧ e.2.2.1 ∈ orbL GD e.2.1 ∧
      BadW BL (Code.mul (Code.mul (rep GD e.1) e.2.2.1) (rep GD e.1)) e.2.2.2 := by
  obtain ⟨hlt, rfl⟩ := bK_basic hb
  intro e he
  obtain ⟨a, b, x, w⟩ := e
  unfold hbK at hbb
  rw [allK_gl, List.all_eq_true] at hbb
  have h1 := hbb _ he
  simp only [andB_gl, Bool.and_eq_true, blt_gl, letB_gl, memN_gl, orb_gl, orb2_gl, rep_gl] at h1
  obtain ⟨ha, hb', hx, hw⟩ := h1
  refine ⟨ha, hb', hx, ?_⟩
  have := badW_gl (lt64 hlt) hw
  rwa [CFSG.KC.GL62.LS.cmulK_eq, CFSG.KC.GL62.LS.cmulK_eq] at this

theorem lensK_gl (GD : List (ℕ × List ℕ)) :
    List.rec (motive := fun _ => List ℕ) List.nil
      (fun e _ ih => List.cons e.2.length ih) GD = GD.map fun e => e.2.length := by
  induction GD with
  | nil => rfl
  | cons x t ih =>
    change x.2.length :: _ = _
    rw [ih]
    rfl

theorem flat_getD (n : ℕ) : ∀ (H : List (List ℕ)), (∀ r ∈ H, r.length = n) →
    ∀ a < H.length, ∀ b < n, H.flatten.getD (n * a + b) 0 = (H.getD a []).getD b 0 := by
  intro H
  induction H with
  | nil => intro _ a ha; simp at ha
  | cons r t ih =>
    intro hr a ha b hb
    have hrl := hr r List.mem_cons_self
    rw [List.flatten_cons]
    cases a with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      rfl
    | succ a =>
      have e : n * (a + 1) + b = n + (n * a + b) := by ring
      rw [e, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        ← List.getD_eq_getElem?_getD]
      have e2 : n + (n * a + b) - r.length = n * a + b := by omega
      rw [e2, ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) a (by simpa using ha) b hb]
      rfl

noncomputable def orRec (p : ℕ → Bool) (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun b acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.lor acc (g b)) (p b)) n

theorem orRec_gl (p : ℕ → Bool) (g : ℕ → ℕ) (n j : ℕ) :
    (orRec p g n).testBit j = true ↔ ∃ b < n, p b = true ∧ (g b).testBit j = true := by
  induction n with
  | zero => simp [orRec]
  | succ n ih =>
    change (Bool.rec (motive := fun _ => ℕ) (orRec p g n) (Nat.lor (orRec p g n) (g n))
      (p n)).testBit j = true ↔ _
    cases hp : p n
    · change (orRec p g n).testBit j = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨b, hb, h1, h2⟩
        exact ⟨b, by omega, h1, h2⟩
      · rintro ⟨b, hb, h1, h2⟩
        have hbn : b ≠ n := fun e => by
          subst e
          rw [hp] at h1
          exact Bool.false_ne_true h1
        exact ⟨b, by omega, h1, h2⟩
    · change (orRec p g n ||| g n).testBit j = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨b, hb, h1, h2⟩ | h2)
        · exact ⟨b, by omega, h1, h2⟩
        · exact ⟨n, by omega, hp, h2⟩
      · rintro ⟨b, hb, h1, h2⟩
        by_cases hbn : b = n
        · subst hbn
          exact Or.inr h2
        · exact Or.inl ⟨b, by omega, h1, h2⟩

noncomputable def sumRec (p : ℕ → Bool) (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun b acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.add acc (g b)) (p b)) n

theorem sumRec_gl (p : ℕ → Bool) (g : ℕ → ℕ) (n : ℕ) :
    sumRec p g n = (((List.range n).filter p).map g).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => ℕ) (sumRec p g n) (Nat.add (sumRec p g n) (g n))
      (p n) = _
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ← ih]
    cases hp : p n
    · simp [hp]
    · simp [hp]

theorem rowSum_gl (CT a I : ℕ) :
    rowSum CT a I = (((List.range 17).filter I.testBit).map
      fun b => laneK CT (17 * a + b)).sum := by
  have e : rowSum CT a I = sumRec (bitK I) (fun b => laneK CT (17 * a + b)) 17 := rfl
  have hb : bitK I = I.testBit := funext (bitK_gl I)
  rw [e, sumRec_gl, hb]

theorem sizeK_gl (SP I : ℕ) :
    sizeK SP I = (((List.range 17).filter I.testBit).map fun b => laneK SP b).sum := by
  have e : sizeK SP I = sumRec (bitK I) (fun b => laneK SP b) 17 := rfl
  have hb : bitK I = I.testBit := funext (bitK_gl I)
  rw [e, sumRec_gl, hb]

theorem closeF_gl (HT I j : ℕ) : (closeF HT I).testBit j = true ↔
    ∃ a < 17, I.testBit a = true ∧ ∃ b < 17, I.testBit b = true ∧
      (laneK HT (17 * a + b)).testBit j = true := by
  have e1 : closeF HT I = orRec (bitK I) (fun a => rowOr HT a I) 17 := rfl
  have e2 : ∀ a, rowOr HT a I = orRec (bitK I) (fun b => laneK HT (17 * a + b)) 17 :=
    fun a => rfl
  rw [e1, orRec_gl]
  simp only [e2, orRec_gl, bitK_gl]

theorem andRec_of (q : ℕ → Bool) : ∀ n, (∀ a < n, q a = true) →
    Nat.rec (motive := fun _ => Bool) true (fun a ih => andB (q a) ih) n = true := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    change andB (q n) (Nat.rec (motive := fun _ => Bool) true (fun a ih => andB (q a) ih) n) = true
    rw [andB_gl, h n (by omega), ih fun a ha => h a (by omega)]
    rfl

theorem homK_of {CT I : ℕ} (h : ∀ a < 17, I.testBit a = true → rowSum CT a I = rowSum CT 0 I) :
    homK CT I = true := by
  unfold homK
  rw [letB_gl]
  refine andRec_of (fun a => Bool.rec (motive := fun _ => Bool) true
    (Nat.beq (rowSum CT a I) (rowSum CT 0 I)) (bitK I a)) 17 fun a ha => ?_
  cases hb : bitK I a
  · rfl
  · change Nat.beq (rowSum CT a I) (rowSum CT 0 I) = true
    rw [bitK_gl] at hb
    exact beq_gl.2 (h a ha hb)

theorem famOK_gl (I s : ℕ) : famOK I s = true ↔ (I, s) ∈ famSizesK := by
  unfold famOK
  rw [anyK_gl, List.any_eq_true]
  constructor
  · rintro ⟨⟨a, b⟩, hx, h⟩
    simp only [andB_gl, Bool.and_eq_true, beq_gl] at h
    rw [h.1, h.2]
    exact hx
  · intro h
    refine ⟨(I, s), h, ?_⟩
    simp [andB_gl, beq_gl]

theorem lowbit_one (t : ℕ) : ∀ i j, (t &&& (t ^^^ (t - 1))).testBit i = true →
    (t &&& (t ^^^ (t - 1))).testBit j = true → i = j := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro i j hi hj
    rw [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true] at hi hj
    rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp at hi
      · have d1 : 2 * s / 2 = s := by omega
        have d2 : (2 * s - 1) / 2 = s - 1 := by omega
        cases i with
        | zero =>
          rw [Nat.testBit_zero] at hi
          simp at hi
        | succ i =>
          cases j with
          | zero =>
            rw [Nat.testBit_zero] at hj
            simp at hj
          | succ j =>
            rw [Nat.testBit_succ, Nat.testBit_succ, d1, d2] at hi hj
            have := ih s (by omega) i j
              (by rw [Nat.testBit_and, Nat.testBit_xor, hi.2, hi.1]; rfl)
              (by rw [Nat.testBit_and, Nat.testBit_xor, hj.2, hj.1]; rfl)
            omega
    · have d1 : (2 * s + 1) / 2 = s := by omega
      have d2 : (2 * s + 1 - 1) / 2 = s := by omega
      have key : ∀ k, ((2 * s + 1).testBit k = true ∧
          ((2 * s + 1).testBit k ^^ (2 * s + 1 - 1).testBit k) = true) → k = 0 := by
        intro k hk
        cases k with
        | zero => rfl
        | succ k =>
          rw [Nat.testBit_succ, Nat.testBit_succ, d1, d2, Bool.xor_self] at hk
          exact absurd hk.2 Bool.false_ne_true
      rw [key i hi, key j hj]

theorem search_inv {HT CT SP m : ℕ} (hm : m < 2 ^ 17)
    (hcl : ∀ a < 17, ∀ b < 17, m.testBit a = true → m.testBit b = true →
      ∀ j, (laneK HT (17 * a + b)).testBit j = true → m.testBit j = true)
    (hhom : homK CT m = true) : ∀ (fuel I O : ℕ), search HT CT SP fuel I O = true →
      (∀ j, I.testBit j = true → m.testBit j = true) →
      (∀ j, m.testBit j = true → O.testBit j = true → False) → famOK m (sizeK SP m) = true := by
  intro fuel
  induction fuel with
  | zero => intro I O h; exact absurd h Bool.false_ne_true
  | succ n ih =>
    intro I O h hI hO
    have hF : ∀ j, (closeF HT I).testBit j = true → m.testBit j = true := by
      intro j hj
      obtain ⟨a, ha, hia, b, hb, hib, hab⟩ := (closeF_gl HT I j).1 hj
      exact hcl a ha b hb (hI a hia) (hI b hib) j hab
    have hm17 : m.testBit 17 = false := Nat.testBit_lt_two_pow hm
    change letB (closeF HT I) (fun F => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (letB (Nat.lor I O) fun U => Bool.rec (motive := fun _ => Bool)
            (letB (Nat.xor U 131071) fun t => letB (Nat.land t (Nat.xor t (Nat.sub t 1))) fun v =>
              andB (letB (Nat.lor I v) fun I' => search HT CT SP n I' O)
                (letB (Nat.lor O v) fun O' => search HT CT SP n I O'))
            (orB (notB (homK CT I)) (famOK I (sizeK SP I)))
            (Nat.beq U 131071))
          (letB (Nat.lor I F) fun I' => search HT CT SP n I' O)
          (notB (Nat.beq (Nat.lor I F) I)))
        true (orB (bitK F 17) (Nat.blt 0 (Nat.land F O)))) = true at h
    simp only [letB_gl] at h
    cases h1 : orB (bitK (closeF HT I) 17) (Nat.blt 0 (Nat.land (closeF HT I) O))
    · rw [h1] at h
      change Bool.rec (motive := fun _ => Bool) _ _ (notB (Nat.beq (Nat.lor I (closeF HT I)) I))
        = true at h
      cases h2 : notB (Nat.beq (Nat.lor I (closeF HT I)) I)
      · rw [h2] at h
        change Bool.rec (motive := fun _ => Bool) _ _ (Nat.beq (Nat.lor I O) 131071) = true at h
        cases h3 : Nat.beq (Nat.lor I O) 131071
        · rw [h3] at h
          change andB (search HT CT SP n (Nat.lor I (Nat.land (Nat.xor (Nat.lor I O) 131071)
            (Nat.xor (Nat.xor (Nat.lor I O) 131071) (Nat.sub (Nat.xor (Nat.lor I O) 131071) 1))))
            O) (search HT CT SP n I (Nat.lor O (Nat.land (Nat.xor (Nat.lor I O) 131071)
            (Nat.xor (Nat.xor (Nat.lor I O) 131071) (Nat.sub (Nat.xor (Nat.lor I O) 131071) 1)))))
            = true at h
          rw [andB_gl, Bool.and_eq_true] at h
          generalize hv : Nat.land (Nat.xor (Nat.lor I O) 131071)
            (Nat.xor (Nat.xor (Nat.lor I O) 131071) (Nat.sub (Nat.xor (Nat.lor I O) 131071) 1)) = v
            at h
          have hv1 : ∀ i j, v.testBit i = true → v.testBit j = true → i = j := by
            rw [← hv]
            exact lowbit_one _
          by_cases hvm : ∃ i, v.testBit i = true ∧ m.testBit i = true
          · obtain ⟨i, hvi, hmi⟩ := hvm
            refine ih _ _ h.1 (fun j hj => ?_) hO
            change (I ||| v).testBit j = true at hj
            rw [Nat.testBit_or, Bool.or_eq_true] at hj
            rcases hj with hj | hj
            · exact hI j hj
            · rw [← hv1 i j hvi hj]
              exact hmi
          · refine ih _ _ h.2 hI (fun j hmj hj => ?_)
            change (O ||| v).testBit j = true at hj
            rw [Nat.testBit_or, Bool.or_eq_true] at hj
            rcases hj with hj | hj
            · exact hO j hmj hj
            · exact hvm ⟨j, hj, hmj⟩
        · rw [h3] at h
          change orB (notB (homK CT I)) (famOK I (sizeK SP I)) = true at h
          have hU := beq_gl.1 h3
          have hmI : m = I := by
            apply Nat.eq_of_testBit_eq
            intro j
            have hUj := congrArg (fun x => Nat.testBit x j) hU
            change (I ||| O).testBit j = _ at hUj
            rw [Nat.testBit_or] at hUj
            by_cases hj : j < 17
            · have h131 : (131071 : ℕ).testBit j = true := by
                interval_cases j <;> rfl
              rw [h131, Bool.or_eq_true] at hUj
              cases hIj : I.testBit j
              · rw [hIj] at hUj
                have hOj : O.testBit j = true := hUj.resolve_left Bool.false_ne_true
                cases hmj : m.testBit j
                · rfl
                · exact absurd (hO j hmj hOj) id
              · exact hI j hIj
            · have h131 : (131071 : ℕ).testBit j = false :=
                Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : (131071 : ℕ) < 2 ^ 17)
                  (Nat.pow_le_pow_right (by norm_num) (by omega)))
              rw [h131, Bool.or_eq_false_iff] at hUj
              rw [hUj.1]
              exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hm
                (Nat.pow_le_pow_right (by norm_num) (by omega)))
          subst hmI
          rw [orB_gl, notB_gl, hhom] at h
          simpa using h
      · rw [h2] at h
        change search HT CT SP n (Nat.lor I (closeF HT I)) O = true at h
        refine ih _ _ h (fun j hj => ?_) hO
        change (I ||| closeF HT I).testBit j = true at hj
        rw [Nat.testBit_or, Bool.or_eq_true] at hj
        rcases hj with hj | hj
        · exact hI j hj
        · exact hF j hj
    · exfalso
      rw [orB_gl, Bool.or_eq_true, bitK_gl, blt_gl] at h1
      rcases h1 with h1 | h1
      · rw [hF 17 h1] at hm17
        exact Bool.false_ne_true hm17.symm
      · have hne : Nat.land (closeF HT I) O ≠ 0 := by omega
        apply hne
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.zero_testBit]
        change (closeF HT I &&& O).testBit j = false
        rw [Nat.testBit_and]
        cases hFj : (closeF HT I).testBit j
        · rfl
        · cases hOj : O.testBit j
          · rfl
          · exact absurd (hO j (hF j hFj) hOj) id

theorem elimK_sound (h : elimK GD H C = true) (hg : goodK BP BIP GD = true)
    (hb : bK BL BIL BP BIP BT = true) {m : ℕ} (hm : m < 2 ^ 17)
    (h0 : m.testBit 0 = true)
    (hclosed : ∀ a < 17, ∀ b < 17, m.testBit a = true → m.testBit b = true →
      tab H a b &&& m = tab H a b)
    (hhom : ∀ a < 17, m.testBit a = true →
      ((memOf m).map fun b => tab C a b).sum = ((memOf m).map fun b => tab C 0 b).sum) :
    (m, ((memOf m).map fun b => (orbL GD b).length).sum) ∈ famSizesK := by
  obtain ⟨hlen, -, -, hp⟩ := goodK_sound hg hb
  unfold elimK at h
  simp only [andB_gl, Bool.and_eq_true, beq_gl, lenK_gl, allK_gl, List.all_eq_true, lenN_gl,
    blt_gl, letB_gl, flatK_gl] at h
  obtain ⟨hH, hHr, hC, hCr, hHb, hCb, hs⟩ := h
  rw [lensK_gl] at hs
  have hHT : ∀ a < 17, ∀ b < 17, laneK (packL H.flatten) (17 * a + b) = tab H a b := by
    intro a ha b hb'
    rw [CFSG.KC.GL62.LS.laneK_packL (fun x hx => lt_of_lt_of_le (hHb x hx) (by norm_num)),
      flat_getD 17 H hHr a (by omega) b hb']
    rfl
  have hCT : ∀ a < 17, ∀ b < 17, laneK (packL C.flatten) (17 * a + b) = tab C a b := by
    intro a ha b hb'
    rw [CFSG.KC.GL62.LS.laneK_packL (fun x hx => lt_of_lt_of_le (hCb x hx) (by norm_num)),
      flat_getD 17 C hCr a (by omega) b hb']
    rfl
  have hSl : ∀ x ∈ GD.map (fun e => e.2.length), x < 2 ^ 64 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have := (hp i (by omega)).2.2.2.2.1
    unfold orbL at this
    rw [getD_eq _ _ i hi] at this
    rw [this]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num)
  have hSP : ∀ b < 17, laneK (packL (GD.map fun e => e.2.length)) b = (orbL GD b).length := by
    intro b hb'
    rw [CFSG.KC.GL62.LS.laneK_packL hSl, getD_map_lt GD _ (0, []) b (by omega)]
    rfl
  have hmem : ∀ a, m.testBit a = true → a < 17 := fun a ha => by
    by_contra hge
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
      (by omega)))] at ha
    exact Bool.false_ne_true ha
  have hcl : ∀ a < 17, ∀ b < 17, m.testBit a = true → m.testBit b = true →
      ∀ j, (laneK (packL H.flatten) (17 * a + b)).testBit j = true → m.testBit j = true := by
    intro a ha b hb' hma hmb j hj
    rw [hHT a ha b hb', ← hclosed a ha b hb' hma hmb, Nat.testBit_and] at hj
    simp only [Bool.and_eq_true] at hj
    exact hj.2
  have hrow : ∀ a < 17, rowSum (packL C.flatten) a m =
      ((memOf m).map fun b => tab C a b).sum := by
    intro a ha
    rw [rowSum_gl, memOf]
    congr 1
    refine List.map_congr_left fun b hb' => ?_
    exact hCT a ha b (List.mem_range.1 (List.mem_of_mem_filter hb'))
  have hhomK : homK (packL C.flatten) m = true := by
    apply homK_of
    intro a ha hma
    rw [hrow a ha, hrow 0 (by norm_num)]
    exact hhom a ha hma
  have hfam := search_inv hm hcl hhomK 40 1 0 hs (fun j hj => by
      rcases j with _ | j
      · exact h0
      · rw [Nat.testBit_succ] at hj
        simp at hj)
    (fun j _ hj => by simp at hj)
  rw [famOK_gl, sizeK_gl] at hfam
  have e : (((List.range 17).filter m.testBit).map fun b =>
      laneK (packL (GD.map fun e => e.2.length)) b) =
      (memOf m).map fun b => (orbL GD b).length := by
    unfold memOf
    refine List.map_congr_left fun b hb' => ?_
    exact hSP b (List.mem_range.1 (List.mem_of_mem_filter hb'))
  rwa [e] at hfam

theorem famK_sound (h : famK BP GD F = true) (hb : bK BL BIL BP BIP BT = true) :
    ∀ f ∈ F, f.2.1 < 17 ∧ f.1.testBit f.2.1 = true ∧ f.2.2.1 ∈ orbL GD f.2.1 ∧
      ∀ p, f.1.testBit p = true → p < 17 ∧ ∃ w : List ℕ, (∀ a ∈ w, a ≤ 336) ∧
        Code.mul (wordV BL f.2.2.1 w) 38959071361 =
          Code.mul (rep GD p) (wordV BL f.2.2.1 w) := by
  obtain ⟨hlt, rfl⟩ := bK_basic hb
  intro f hf
  obtain ⟨mask, q, g, ents⟩ := f
  unfold famK at h
  rw [allK_gl, List.all_eq_true] at h
  have h1 := h _ hf
  simp only [andB_gl, Bool.and_eq_true, blt_gl, bitK_gl, memN_gl, orb_gl, orb2_gl, beq_gl, allK_gl,
    List.all_eq_true] at h1
  obtain ⟨hq, hm, hg, hmask, hents⟩ := h1
  refine ⟨hq, hm, hg, fun p hp => ?_⟩
  rw [hmask, bitsK_gl, fstK_gl, List.mem_map] at hp
  obtain ⟨⟨p', w⟩, hpw, rfl⟩ := hp
  have h2 := hents _ hpw
  simp only [andB_gl, Bool.and_eq_true, blt_gl, letB_gl, beq_gl] at h2
  obtain ⟨hp, hw, he⟩ := h2
  rw [CFSG.KC.GL62.LS.cmulK_eq, CFSG.KC.GL62.LS.cmulK_eq, wordK_gl (lt64 hlt), rep_gl] at he
  exact ⟨hp, w, lettersK_gl hw, he⟩

end CFSG.KC.GL62

end
