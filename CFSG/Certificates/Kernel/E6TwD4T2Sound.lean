module

public import Certificates.Data.Kernel.E6TwD4T2.Kit
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

set_option exponentiation.threshold 800

public section

namespace CFSG.KD.E6TwD4T2

open Finset

@[expose] def dot3 (k : ℕ) (v : List ℕ) : ℕ :=
  (∑ j ∈ Finset.range 6, (k / 3 ^ j % 3) * v.getD j 0) % 3

theorem bit_eq (m k : ℕ) : bit m k = m.testBit k := by
  have e : bit m k = Nat.blt 0 (m &&& 2 ^ k) := by
    unfold bit
    simp only [Nat.land_eq, Nat.shiftLeft_eq', Nat.one_shiftLeft]
  rw [e]
  cases h : m.testBit k
  · have h0 : m &&& 2 ^ k = 0 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hik : k = i
      · subst hik; simp [h]
      · simp [hik]
    rw [h0]; rfl
  · have h2 : (m &&& 2 ^ k).testBit k = true := by
      rw [Nat.testBit_and, h, Nat.testBit_two_pow_self]; rfl
    have hp : 0 < m &&& 2 ^ k := lt_of_lt_of_le (Nat.two_pow_pos k) (Nat.ge_two_pow_of_testBit h2)
    rw [← Nat.blt_eq] at hp
    exact hp

theorem full_eq : full = 2 ^ 729 - 1 := by
  unfold full
  rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]
  rfl

theorem full_lt : full < 2 ^ 729 := by
  rw [full_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos

theorem testBit_full (i : ℕ) : full.testBit i = decide (i < 729) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem get_testBit (S s k : ℕ) :
    (get S s).testBit k = (decide (k < 729) && S.testBit (s * 729 + k)) := by
  change (S >>> (s * 729) &&& full).testBit k = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_full, Bool.and_comm]

theorem get_lt (S s : ℕ) : get S s < 2 ^ 729 := Nat.and_lt_two_pow _ full_lt

theorem testBit_hi {a : ℕ} (ha : a < 2 ^ 729) {i : ℕ} (hi : 729 ≤ i) : a.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi))

theorem get_pack {a b c : ℕ} (ha : a < 2 ^ 729) (hb : b < 2 ^ 729) (k : ℕ) :
    (get (pack a b c) 0).testBit k = (decide (k < 729) && a.testBit k) ∧
    (get (pack a b c) 1).testBit k = (decide (k < 729) && b.testBit k) ∧
    (get (pack a b c) 2).testBit k = (decide (k < 729) && c.testBit k) := by
  rw [get_testBit, get_testBit, get_testBit]
  by_cases hk : k < 729
  · have i0 : 0 * 729 + k = k := by clear ha hb; omega
    have i1 : 1 * 729 + k = 729 + k := by clear ha hb; omega
    have i2 : 2 * 729 + k = 1458 + k := by clear ha hb; omega
    have l1 : 729 ≤ 729 + k := by clear ha hb; omega
    have l2 : 729 ≤ 1458 + k := by clear ha hb; omega
    have ha1 := testBit_hi ha l1
    have ha2 := testBit_hi ha l2
    have hb1 := testBit_hi hb l1
    have hb2 := testBit_hi hb l2
    have j1 : 729 + k - 729 = k := by clear ha hb; omega
    have j2 : 1458 + k - 729 = 729 + k := by
      rw [show 1458 = 729 + 729 from rfl, Nat.add_assoc, Nat.add_sub_cancel_left]
    have j3 : 1458 + k - 1458 = k := by rw [Nat.add_sub_cancel_left]
    have d1 : decide (k ≥ 729) = false := decide_eq_false (by clear ha hb; omega)
    have d2 : decide (k ≥ 1458) = false := decide_eq_false (by clear ha hb; omega)
    have d3 : decide (729 + k ≥ 1458) = false := decide_eq_false (by clear ha hb; omega)
    have d4 : decide (729 + k ≥ 729) = true := decide_eq_true (by clear ha hb; omega)
    have d5 : decide (1458 + k ≥ 729) = true := decide_eq_true (by clear ha hb; omega)
    have d6 : decide (1458 + k ≥ 1458) = true := decide_eq_true (by clear ha hb; omega)
    have e : pack a b c = a ||| (b <<< 729 ||| c <<< 1458) := rfl
    simp only [i0, i1, i2, e, Nat.testBit_or, Nat.testBit_shiftLeft, ha1, ha2, hb2, j1, j2, j3,
      d1, d2, d3, d4, d5, d6, hb1, hk, decide_true,
      Bool.true_and, Bool.false_and, Bool.or_false, Bool.false_or]
    all_goals trivial
  · simp [hk]

def Rep (S : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ s < 3, ∀ k, (get S s).testBit k = (decide (k < 729) && decide (f k % 3 = s))

theorem rep_congr {S : ℕ} {f g : ℕ → ℕ} (h : Rep S f) (e : ∀ k, f k % 3 = g k % 3) : Rep S g := by
  intro s hs k; rw [h s hs k, e k]

theorem rep_full : Rep full fun _ => 0 := by
  intro s hs k
  rw [get_testBit, testBit_full]
  interval_cases s <;> by_cases hk : k < 729 <;> simp [hk] <;> omega

theorem land_lt {A P : ℕ} (h : A < 2 ^ 729) : Nat.land A P < 2 ^ 729 := by
  rw [Nat.land_eq, Nat.and_comm]; exact Nat.and_lt_two_pow _ h

theorem pack_rep {a b c : ℕ} {g : ℕ → ℕ} (ha : a < 2 ^ 729) (hb : b < 2 ^ 729)
    (h : ∀ k < 729, a.testBit k = decide (g k % 3 = 0) ∧ b.testBit k = decide (g k % 3 = 1) ∧
      c.testBit k = decide (g k % 3 = 2)) : Rep (pack a b c) g := by
  intro s hs k
  obtain ⟨g0, g1, g2⟩ := get_pack (c := c) ha hb k
  by_cases hk : k < 729
  · obtain ⟨h0, h1, h2⟩ := h k hk
    interval_cases s
    · rw [g0, h0]
    · rw [g1, h1]
    · rw [g2, h2]
  · interval_cases s <;> simp [g0, g1, g2, hk]

theorem rec_and_iff (f : ℕ → Bool) (n : ℕ) :
    Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.and ih (f k)) n = true ↔
      ∀ k < n, f k = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    change (Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.and ih (f k)) n && f n) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h; exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem lrec_and_iff {α : Type} (g : α → Bool) (L : List α) :
    List.rec (motive := fun _ => Bool) true (fun x _ ih => Bool.and ih (g x)) L = true ↔
      ∀ x ∈ L, g x = true := by
  induction L with
  | nil => simp
  | cons x L ih =>
    change (List.rec (motive := fun _ => Bool) true (fun x _ ih => Bool.and ih (g x)) L && g x) = true ↔ _
    rw [Bool.and_eq_true, ih]; simp [and_comm]

theorem lrec_or_iff {α : Type} (g : α → Bool) (L : List α) :
    List.rec (motive := fun _ => Bool) false (fun x _ ih => Bool.or ih (g x)) L = true ↔
      ∃ x ∈ L, g x = true := by
  induction L with
  | nil => simp
  | cons x L ih =>
    change (List.rec (motive := fun _ => Bool) false (fun x _ ih => Bool.or ih (g x)) L || g x) = true ↔ _
    rw [Bool.or_eq_true, ih]; simp [or_comm]

theorem land_fold_tb {α : Type} (B : ℕ) (g : α → ℕ) (L : List α) (i : ℕ) :
    (List.rec (motive := fun _ => ℕ) B (fun x _ ih => Nat.land ih (g x)) L).testBit i = true ↔
      B.testBit i = true ∧ ∀ x ∈ L, (g x).testBit i = true := by
  induction L with
  | nil => simp
  | cons x L ih =>
    change ((List.rec (motive := fun _ => ℕ) B (fun x _ ih => Nat.land ih (g x)) L) &&& g x).testBit i
      = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, ih]; simp only [List.mem_cons, forall_eq_or_imp]; tauto

theorem lor_fold_tb {α : Type} (g : α → ℕ) (L : List α) (i : ℕ) :
    (List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.lor ih (g x)) L).testBit i = true ↔
      ∃ x ∈ L, (g x).testBit i = true := by
  induction L with
  | nil => simp
  | cons x L ih =>
    change ((List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.lor ih (g x)) L) ||| g x).testBit i
      = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨y, hy, h⟩ | h)
      · exact ⟨y, List.mem_cons_of_mem _ hy, h⟩
      · exact ⟨x, List.mem_cons_self, h⟩
    · rintro ⟨y, hy, h⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Or.inr h
      · exact Or.inl ⟨y, hy, h⟩

theorem planes_spec (hP : planesOK = true) {j a : ℕ} (hj : j < 6) (ha : a < 3) :
    pl j a < 2 ^ 729 ∧ ∀ k < 729, (pl j a).testBit k = decide (k / 3 ^ j % 3 = a) := by
  unfold planesOK at hP
  rw [rec_and_iff] at hP
  have h1 := hP j hj
  beta_reduce at h1
  rw [rec_and_iff] at h1
  have h2 := h1 a ha
  beta_reduce at h2
  rw [Bool.and_eq_true] at h2
  obtain ⟨hlt, h3⟩ := h2
  refine ⟨?_, fun k hk => ?_⟩
  · have := Nat.blt_eq.mp hlt
    rwa [Nat.shiftLeft_eq', Nat.one_shiftLeft] at this
  · rw [rec_and_iff] at h3
    have h4 := h3 k hk
    beta_reduce at h4
    have hb : ∀ b c : Bool, beqB b c = true → b = c := by decide
    have e1 : Nat.beq (Nat.mod (Nat.div k (Nat.pow 3 j)) 3) a = decide (k / 3 ^ j % 3 = a) := by
      rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]
      exact Iff.rfl
    rw [← bit_eq, hb _ _ h4, e1]

theorem step_rep (hP : planesOK = true) {j x S : ℕ} {f : ℕ → ℕ} (hj : j < 6) (hx : x < 3)
    (hS : Rep S f) : Rep (stepL j x S) (fun k => f k + k / 3 ^ j % 3 * x) := by
  have hb : ∀ (A P B Q C R : ℕ), A < 2 ^ 729 → B < 2 ^ 729 → C < 2 ^ 729 →
      or3 (Nat.land A P) (Nat.land B Q) (Nat.land C R) < 2 ^ 729 := by
    intro A P B Q C R hA hB hC
    exact Nat.or_lt_two_pow (land_lt hA) (Nat.or_lt_two_pow (land_lt hB) (land_lt hC))
  have hl := get_lt S
  interval_cases x
  · intro s hs k
    change (get S s).testBit k = _
    rw [hS s hs k]; simp
  · change Rep (st1 (get S 0) (get S 1) (get S 2) (pl j 0) (pl j 1) (pl j 2)) _
    refine pack_rep (hb _ _ _ _ _ _ (hl _) (hl _) (hl _)) (hb _ _ _ _ _ _ (hl _) (hl _) (hl _))
      fun k hk => ?_
    have hd : k / 3 ^ j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    simp only [or3, Nat.lor_eq, Nat.land_eq, Nat.testBit_or, Nat.testBit_and,
      hS 0 (by norm_num) k, hS 1 (by norm_num) k, hS 2 (by norm_num) k,
      (planes_spec hP hj (a := 0) (by norm_num)).2 k hk, (planes_spec hP hj (a := 1) (by norm_num)).2 k hk,
      (planes_spec hP hj (a := 2) (by norm_num)).2 k hk, hk, decide_true, Bool.true_and]
    generalize k / 3 ^ j % 3 = dd at hd ⊢
    generalize f k = F
    refine ⟨?_, ?_, ?_⟩ <;> rw [Bool.eq_iff_iff] <;>
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · change Rep (st2 (get S 0) (get S 1) (get S 2) (pl j 0) (pl j 1) (pl j 2)) _
    refine pack_rep (hb _ _ _ _ _ _ (hl _) (hl _) (hl _)) (hb _ _ _ _ _ _ (hl _) (hl _) (hl _))
      fun k hk => ?_
    have hd : k / 3 ^ j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    simp only [or3, Nat.lor_eq, Nat.land_eq, Nat.testBit_or, Nat.testBit_and,
      hS 0 (by norm_num) k, hS 1 (by norm_num) k, hS 2 (by norm_num) k,
      (planes_spec hP hj (a := 0) (by norm_num)).2 k hk, (planes_spec hP hj (a := 1) (by norm_num)).2 k hk,
      (planes_spec hP hj (a := 2) (by norm_num)).2 k hk, hk, decide_true, Bool.true_and]
    generalize k / 3 ^ j % 3 = dd at hd ⊢
    generalize f k = F
    refine ⟨?_, ?_, ?_⟩ <;> rw [Bool.eq_iff_iff] <;>
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega

theorem lvl_rep (hP : planesOK = true) :
    ∀ (v : List ℕ) (j S : ℕ) (f : ℕ → ℕ), j + v.length ≤ 6 → (∀ x ∈ v, x < 3) → Rep S f →
      Rep (List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
          (fun x _ ih j S => ih (Nat.succ j) (stepL j x S)) v j S)
        (fun k => f k + ∑ i ∈ range v.length, k / 3 ^ (j + i) % 3 * v.getD i 0) := by
  intro v
  induction v with
  | nil =>
    intro j S f _ _ hS
    exact rep_congr hS (fun k => by simp)
  | cons x v ih =>
    intro j S f hlen hv hS
    have hx : x < 3 := hv x (by simp)
    have h := ih (j + 1) (stepL j x S) _ (by simp at hlen; omega) (fun y hy => hv y (by simp [hy]))
      (step_rep hP (by simp at hlen; omega) hx hS)
    refine rep_congr h (fun k => congrArg (· % 3) ?_)
    beta_reduce
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [Finset.sum_congr rfl (fun i _ => by rw [show j + 1 + i = j + (i + 1) by omega])]
    ring

def Good (v : List ℕ) : Prop := v.length ≤ 6 ∧ ∀ x ∈ v, x < 3

theorem dot3_eq {v : List ℕ} (hv : v.length ≤ 6) (k : ℕ) :
    dot3 k v = (∑ i ∈ range v.length, k / 3 ^ (0 + i) % 3 * v.getD i 0) % 3 := by
  unfold dot3
  obtain ⟨m, hm⟩ : ∃ m, 6 = v.length + m := ⟨6 - v.length, by omega⟩
  rw [hm, Finset.sum_range_add]
  have : ∑ x ∈ range m, k / 3 ^ (v.length + x) % 3 * v.getD (v.length + x) 0 = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
  rw [this, Nat.add_zero]
  simp only [Nat.zero_add]

theorem lvl_tb (hP : planesOK = true) {v : List ℕ} (hv : Good v) {s : ℕ} (hs : s < 3) (k : ℕ) :
    (get (lvl v) s).testBit k = true ↔ k < 729 ∧ dot3 k v = s := by
  have h := lvl_rep hP v 0 full (fun _ => 0) (by simpa using hv.1) hv.2 rep_full
  have e : lvl v = List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
      (fun x _ ih j S => ih (Nat.succ j) (stepL j x S)) v 0 full := rfl
  rw [e, h s hs k, dot3_eq hv.1]
  simp

theorem dot3_lt (k : ℕ) (v : List ℕ) : dot3 k v < 3 := Nat.mod_lt _ (by norm_num)

theorem lv_lvl (hP : planesOK = true) {v : List ℕ} (hv : Good v) {k : ℕ} (hk : k < 729) :
    lv (lvl v) k = dot3 k v := by
  have hb : ∀ s < 3, bit (get (lvl v) s) k = decide (dot3 k v = s) := by
    intro s hs
    rw [bit_eq, Bool.eq_iff_iff, lvl_tb hP hv hs]; simp [hk]
  unfold lv
  rw [hb 1 (by norm_num), hb 2 (by norm_num)]
  have := dot3_lt k v
  generalize dot3 k v = d at this ⊢
  interval_cases d <;> rfl

theorem wv_good (r3 : List (List ℕ)) (t : List ℕ) : ∀ w ∈ wv r3 t, Good w := by
  intro w hw
  simp only [wv, List.mem_map, List.mem_range] at hw
  obtain ⟨j, _, rfl⟩ := hw
  refine ⟨by simp, fun x hx => ?_⟩
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact Nat.mod_lt _ (by norm_num)

theorem r3_good {r3 : List (List ℕ)} (hr : r3OK r3 = true) (p : ℕ) : Good (r3.getD p []) := by
  simp only [r3OK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at hr
  rw [List.getD_eq_getElem?_getD]
  cases h : r3[p]? with
  | none => exact ⟨by simp, by simp⟩
  | some r =>
    have hm := hr.2 r (List.mem_of_getElem? h)
    exact ⟨by simp [hm.1], by simpa using hm.2⟩

theorem pairsK_sound {r3 wts wlv : List (List ℕ)} {sig sigL : List ℕ} {G : ℕ}
    (hP : planesOK = true) (hr : r3OK r3 = true) (htab : tabOK r3 wts wlv = true)
    (hsig : sigOK r3 sig sigL = true) (hG : gOK wlv G = true) (h : pairsK wlv sigL G 729 = true) :
    ∀ k₁ < 729, ∀ k₂ < 729, (∃ ws ∈ wts.map (wv r3), ∀ w ∈ ws, dot3 k₁ w = 0) ∨
      (∃ p ∈ sig, dot3 k₁ (r3.getD p []) = 0 ∧ dot3 k₂ (r3.getD p []) = 0) ∨
      (∃ ws ∈ wts.map (wv r3), ∀ w ∈ ws, dot3 k₂ w = 0) ∨
      (∃ ws ∈ wts.map (wv r3), ∀ w ∈ ws, dot3 k₂ w = (3 - dot3 k₁ w) % 3) ∨
      (∃ ws ∈ wts.map (wv r3), ∀ w ∈ ws, dot3 k₂ w = dot3 k₁ w) := by
  intro k₁ hk₁ k₂ hk₂
  have htab' : (wts.map (wv r3)).map (fun M => M.map lvl) = wlv := beq_iff_eq.1 htab
  have hsig' : sig.map (fun p => get (lvl (r3.getD p [])) 0) = sigL := beq_iff_eq.1 hsig
  have hG' : gOf wlv = G := Nat.beq_eq.mp hG
  have hgood : ∀ ws ∈ wts.map (wv r3), ∀ w ∈ ws, Good w := by
    intro ws hws w hw
    obtain ⟨t, _, rfl⟩ := List.mem_map.1 hws
    exact wv_good r3 t w hw
  unfold pairsK at h
  rw [rec_and_iff] at h
  have hc : condK wlv sigL G k₁ = true := h k₁ hk₁
  unfold condK at hc
  rw [Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · left
    obtain ⟨M, hM, hz⟩ := (lrec_or_iff _ wlv).1 hc
    rw [← htab'] at hM
    obtain ⟨ws, hws, rfl⟩ := List.mem_map.1 hM
    refine ⟨ws, hws, fun w hw => ?_⟩
    have := (lrec_and_iff (fun S => Nat.beq (lv S k₁) 0) _).1 hz (lvl w) (List.mem_map_of_mem hw)
    rw [Nat.beq_eq, lv_lvl hP (hgood ws hws w hw) hk₁] at this
    exact this
  · have hX := Nat.beq_eq.mp hc
    have hb : (Nat.lor (Nat.lor (rmask sigL k₁) G)
        (List.rec (motive := fun _ => ℕ) 0
          (fun M _ ih => Nat.lor ih (Nat.lor (tpm M k₁) (tmm M k₁))) wlv)).testBit k₂ = true := by
      rw [hX, testBit_full]; simpa using hk₂
    simp only [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true] at hb
    rcases hb with (hb | hb) | hb
    ·
      right; left
      have key : ∀ (L : List ℕ), (rmask L k₁).testBit k₂ = true →
          ∃ m ∈ L, bit m k₁ = true ∧ m.testBit k₂ = true := by
        intro L
        induction L with
        | nil => intro h0; simp [rmask] at h0
        | cons m L ih =>
          intro h1
          change (Bool.rec (motive := fun _ => ℕ) (rmask L k₁) (Nat.lor (rmask L k₁) m)
            (bit m k₁)).testBit k₂ = true at h1
          cases hm : bit m k₁
          · rw [hm] at h1
            obtain ⟨m', hm', h2⟩ := ih h1
            exact ⟨m', List.mem_cons_of_mem _ hm', h2⟩
          · rw [hm] at h1
            change (rmask L k₁ ||| m).testBit k₂ = true at h1
            rw [Nat.testBit_or, Bool.or_eq_true] at h1
            rcases h1 with h1 | h1
            · obtain ⟨m', hm', h2⟩ := ih h1
              exact ⟨m', List.mem_cons_of_mem _ hm', h2⟩
            · exact ⟨m, List.mem_cons_self, hm, h1⟩
      obtain ⟨m, hm, h1, h2⟩ := key sigL hb
      rw [← hsig'] at hm
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      rw [bit_eq, lvl_tb hP (r3_good hr p) (by norm_num)] at h1
      rw [lvl_tb hP (r3_good hr p) (by norm_num)] at h2
      exact ⟨p, hp, h1.2, h2.2⟩
    ·
      right; right; left
      rw [← hG'] at hb
      obtain ⟨M, hM, hz⟩ := (lor_fold_tb _ wlv k₂).1 hb
      rw [← htab'] at hM
      obtain ⟨ws, hws, rfl⟩ := List.mem_map.1 hM
      refine ⟨ws, hws, fun w hw => ?_⟩
      have := ((land_fold_tb full (fun S => get S 0) _ k₂).1 hz).2 (lvl w) (List.mem_map_of_mem hw)
      exact ((lvl_tb hP (hgood ws hws w hw) (by norm_num) k₂).1 this).2
    · obtain ⟨M, hM, hz⟩ := (lor_fold_tb _ wlv k₂).1 hb
      rw [← htab'] at hM
      obtain ⟨ws, hws, rfl⟩ := List.mem_map.1 hM
      simp only [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true] at hz
      rcases hz with hz | hz
      · right; right; right; left
        refine ⟨ws, hws, fun w hw => ?_⟩
        have := ((land_fold_tb full (fun S => get S (neg3 (lv S k₁))) _ k₂).1 hz).2 (lvl w)
          (List.mem_map_of_mem hw)
        rw [lv_lvl hP (hgood ws hws w hw) hk₁] at this
        exact ((lvl_tb hP (hgood ws hws w hw) (Nat.mod_lt _ (by norm_num)) k₂).1 this).2
      · right; right; right; right
        refine ⟨ws, hws, fun w hw => ?_⟩
        have := ((land_fold_tb full (fun S => get S (lv S k₁)) _ k₂).1 hz).2 (lvl w)
          (List.mem_map_of_mem hw)
        rw [lv_lvl hP (hgood ws hws w hw) hk₁] at this
        exact ((lvl_tb hP (hgood ws hws w hw) (dot3_lt _ _) k₂).1 this).2

theorem stabK_sound {r3 elems negs : List (List ℕ)} (hP : planesOK = true) (hr : r3OK r3 = true)
    (hlen : elems.length ≤ negs.length) (h : stabK r3 elems negs = true) :
    ∀ i < elems.length, elems[i]! = [0, 1, 2, 3, 4, 5] ∨
      ∀ k < 729, (∀ w ∈ wv r3 elems[i]!, dot3 k w = 0) →
        ∃ p ∈ negs.getD i [], dot3 k (r3.getD p []) = 0 := by
  intro i hi
  have hzi : i < (elems.zip negs).length := by simp; omega
  have hmem := List.getElem_mem hzi
  have hall := (lrec_and_iff _ _).1 h _ hmem
  rw [List.getElem_zip] at hall
  dsimp only at hall
  rw [getElem!_pos elems i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    Option.getD_some]
  rw [Bool.or_eq_true] at hall
  rcases hall with he | hb
  · exact Or.inl (beq_iff_eq.1 he)
  right
  intro k hk hfix
  by_contra! hne
  have h0 := Nat.beq_eq.mp hb
  have hbit : (badM r3 elems[i] negs[i]).testBit k = true := by
    unfold badM
    rw [land_fold_tb]
    refine ⟨?_, fun p hp => ?_⟩
    · unfold fixM
      rw [land_fold_tb]
      refine ⟨by rw [testBit_full]; simpa using hk, fun w hw => ?_⟩
      exact (lvl_tb hP (wv_good r3 _ w hw) (by norm_num) k).2 ⟨hk, hfix w hw⟩
    · have e : full - get (lvl (r3.getD p [])) 0 = 2 ^ 729 - (get (lvl (r3.getD p [])) 0 + 1) := by
        rw [full_eq, Nat.sub_sub, Nat.add_comm 1]
      rw [Nat.sub_eq, e, Nat.testBit_two_pow_sub_succ (get_lt _ _)]
      have hf : (get (lvl (r3.getD p [])) 0).testBit k = false := by
        rw [Bool.eq_false_iff]
        intro ht
        exact hne p hp ((lvl_tb hP (r3_good hr p) (by norm_num) k).1 ht).2
      rw [hf]
      simp [hk]
  rw [h0, Nat.zero_testBit] at hbit
  exact absurd hbit (by simp)

end CFSG.KD.E6TwD4T2
