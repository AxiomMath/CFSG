module

public import Certificates.Data.Kernel.FixBoundK.Pairs

public section

namespace CFSG.KC.FixBoundK.Pair

open CFSG.KLie.CT CFSG.KC.SortTree

noncomputable abbrev bp (BP k : Nat) : Nat := fget BP k 5

theorem fbkP_bAnd {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem fbkP_bIfT {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem fbkP_bIfF {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = false) : e = true := by
  subst hc
  exact h

theorem fbkP_orB {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem fbkP_notB {a : Bool} (h : notB a = true) : a = false := by
  cases a
  · rfl
  · exact absurd h Bool.false_ne_true

theorem fbkP_beq {a b : Nat} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

theorem fbkP_blt {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem fbkP_ble {a b : Nat} : Nat.ble a b = true ↔ a ≤ b := by rw [Nat.ble_eq]

theorem fbkP_notBeq {a b : Nat} (h : notB (Nat.beq a b) = true) : a ≠ b := by
  intro hab
  have h' := fbkP_notB h
  rw [hab, (fbkP_beq (a := b) (b := b)).2 rfl] at h'
  exact Bool.noConfusion h'

theorem fbkP_strictK (y : Nat) (k : Nat → Bool) : strictK y k = k y := by cases y <;> rfl

theorem fbkP_pw2 (w : Nat) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem fbkP_allN {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    constructor
    · intro h i hi
      cases hf : f n
      · have h' : andB (f n) (allN n f) = true := h
        rw [hf] at h'
        exact absurd h' Bool.false_ne_true
      · have h' : andB (f n) (allN n f) = true := h
        rw [hf] at h'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact ih.1 h' i hi
        · rw [hi]
          exact hf
    · intro h
      have h' : andB (f n) (allN n f) = andB true true := by
        rw [h n (Nat.lt_succ_self n), ih.2 fun i hi => h i (Nat.lt_succ_of_lt hi)]
      exact h'

theorem fbkP_anyN {n : Nat} {f : Nat → Bool} (h : anyN n f = true) : ∃ i < n, f i = true := by
  induction n with
  | zero => exact absurd h Bool.false_ne_true
  | succ n ih =>
    rcases fbkP_orB h with h1 | h1
    · exact ⟨n, Nat.lt_succ_self n, h1⟩
    · obtain ⟨i, hi, hi'⟩ := ih h1
      exact ⟨i, Nat.lt_succ_of_lt hi, hi'⟩

theorem fbkP_nIf_blt (i r a b : Nat) :
    Bool.rec (motive := fun _ => Nat) b a (Nat.blt i r) = if i < r then a else b := by
  by_cases h : i < r
  · rw [if_pos h, fbkP_blt.2 h]
  · rw [if_neg h]
    have hb : Nat.blt i r = false := by
      cases hb : Nat.blt i r
      · rfl
      · exact absurd (fbkP_blt.1 hb) h
    rw [hb]

theorem baseOK_spec {BP nB : Nat} {rec : Nat → Nat} {j : Nat} (h : baseOK BP nB rec j = true)
    (hfix : ∀ k < nB, ap (valF 120 (rec j)) (bp BP k) = bp BP k) : valF 120 (rec j) = idc := by
  rw [baseOK, fbkP_strictK] at h
  rcases fbkP_orB h with h1 | h1
  · have hall : allB BP nB (fun β => Nat.beq (ap (valF 120 (rec j)) β) β) = true :=
      fbkP_allN.2 fun k hk => fbkP_beq.2 (hfix k hk)
    exact absurd ((fbkP_notB h1).symm.trans hall) Bool.false_ne_true
  · exact fbkP_beq.1 h1

theorem invOK_spec {IV IR n i : Nat} {rec : Nat → Nat} (h : invOK IV IR rec n i = true) :
    ivc IV i = valF 120 (rec (fget IR i 10)) ∧
      (∀ p < 24, ap (ivc IV i) (ap (ivc IV i) p) = p) ∧ ivc IV i ≠ idc ∧
      (i + 1 < n → fget IR i 10 < fget IR (i + 1) 10) := by
  rw [invOK, fbkP_strictK] at h
  obtain ⟨h1, h2⟩ := fbkP_bAnd h
  obtain ⟨h2, h3⟩ := fbkP_bAnd h2
  obtain ⟨h3, h4⟩ := fbkP_bAnd h3
  exact ⟨fbkP_beq.1 h1, fun p hp => fbkP_beq.1 (fbkP_allN.1 h2 p hp), fbkP_notBeq h3,
    fun hi => fbkP_blt.1 (fbkP_bIfT h4 (fbkP_blt.2 hi))⟩

theorem cmOK_spec {IV CM BP nB n a : Nat} (h : cmOK IV CM BP nB n a = true) {b : Nat} (hb : b < n)
    (hclr : bit (fget CM a n) b = false) :
    ∃ k < nB, ap (ivc IV a) (ap (ivc IV b) (bp BP k)) ≠ ap (ivc IV b) (ap (ivc IV a) (bp BP k)) := by
  simp only [cmOK, fbkP_strictK] at h
  rcases fbkP_orB (fbkP_allN.1 h b hb) with h1 | h1
  · exact absurd (hclr.symm.trans h1) Bool.false_ne_true
  · have hc := fbkP_notB h1
    refine Classical.byContradiction fun hne => ?_
    have hall : commB BP nB (ivc IV a) (ivc IV b) = true := fbkP_allN.2 fun k hk =>
      fbkP_beq.2 (Classical.byContradiction fun hk' => hne ⟨k, hk, hk'⟩)
    exact absurd (hc.symm.trans hall) Bool.false_ne_true

theorem fbkP_eqDecAux (X : Nat) : ∀ (l : List Nat) (i : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 24))
      (fun v _ ih i => bAnd(Nat.beq (ap X i) v, ih (Nat.succ i))) l i = true →
    i + l.length = 24 ∧ ∀ m < l.length, ap X (i + m) = l.getD m 0
  | [], i, h => ⟨fbkP_beq.1 h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | v :: l, i, h => by
    obtain ⟨h1, h2⟩ := fbkP_bAnd h
    obtain ⟨ih1, ih2⟩ := fbkP_eqDecAux X l (i + 1) h2
    refine ⟨by rw [List.length_cons]; omega, fun m hm => ?_⟩
    cases m with
    | zero =>
      rw [Nat.add_zero, List.getD_cons_zero]
      exact fbkP_beq.1 h1
    | succ m =>
      rw [List.length_cons] at hm
      have e : i + (m + 1) = i + 1 + m := by omega
      rw [e, List.getD_cons_succ]
      exact ih2 m (by omega)

theorem fbkP_gensAux (IV R n : Nat) : ∀ (gl : List (List Nat)) (j : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (rk R))
      (fun g _ ih j => bAnd(Nat.blt (gI R j) n,
        bAnd(eqDec (ivc IV (gI R j)) g, ih (Nat.succ j)))) gl j = true →
    j + gl.length = rk R ∧ ∀ m < gl.length,
      gI R (j + m) < n ∧ eqDec (ivc IV (gI R (j + m))) (gl[m]?.getD []) = true
  | [], j, h => ⟨fbkP_beq.1 h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | g :: gl, j, h => by
    obtain ⟨h1, h2⟩ := fbkP_bAnd h
    obtain ⟨h2, h3⟩ := fbkP_bAnd h2
    obtain ⟨ih1, ih2⟩ := fbkP_gensAux IV R n gl (j + 1) h3
    refine ⟨by rw [List.length_cons]; omega, fun m hm => ?_⟩
    cases m with
    | zero =>
      rw [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some]
      exact ⟨fbkP_blt.1 h1, h2⟩
    | succ m =>
      rw [List.length_cons] at hm
      have e : j + (m + 1) = j + 1 + m := by omega
      rw [e, List.getElem?_cons_succ]
      exact ih2 m (by omega)

theorem repOK_spec {IV RG BP nB n t r : Nat} {gl : List (List Nat)}
    (h : repOK IV RG BP nB n t r gl = true) :
    rk (fget RG t 56) = r ∧ gl.length = r ∧
      (∀ j < r, gI (fget RG t 56) j < n ∧ ∀ p < 24,
        ap (ivc IV (gI (fget RG t 56) j)) p = (gl[j]?.getD []).getD p 0) ∧
      (∀ i < r, ∀ j < i, ∀ k < nB,
        ap (ivc IV (gI (fget RG t 56) i)) (ap (ivc IV (gI (fget RG t 56) j)) (bp BP k)) =
          ap (ivc IV (gI (fget RG t 56) j)) (ap (ivc IV (gI (fget RG t 56) i)) (bp BP k))) ∧
      ∀ μ, 0 < μ → μ < 2 ^ r → ∃ k < nB, pA IV (fget RG t 56) μ (bp BP k) ≠ bp BP k := by
  rw [repOK, fbkP_strictK] at h
  obtain ⟨h1, h2⟩ := fbkP_bAnd h
  obtain ⟨h2, h3⟩ := fbkP_bAnd h2
  obtain ⟨h3, h4⟩ := fbkP_bAnd h3
  have hrk : rk (fget RG t 56) = r := fbkP_beq.1 h1
  obtain ⟨hlen, hgen⟩ := fbkP_gensAux IV (fget RG t 56) n gl 0 h2
  rw [Nat.zero_add, hrk] at hlen
  refine ⟨hrk, hlen, fun j hj => ?_, fun i hi j hj k hk => ?_, fun μ hμ hμr => ?_⟩
  · obtain ⟨hn, hd⟩ := hgen j (hlen ▸ hj)
    rw [Nat.zero_add] at hn hd
    obtain ⟨hl, hv⟩ := fbkP_eqDecAux _ _ 0 hd
    rw [Nat.zero_add] at hl
    refine ⟨hn, fun p hp => ?_⟩
    have := hv p (hl ▸ hp)
    rw [Nat.zero_add] at this
    exact this
  · have hc := fbkP_allN.1 (fbkP_allN.1 h3 i hi) j hj
    simp only [fbkP_strictK] at hc
    exact fbkP_beq.1 (fbkP_allN.1 hc k hk)
  · have hlt : μ - 1 < 2 ^ r - 1 := by omega
    obtain ⟨k, hk, hk'⟩ := fbkP_anyN (fbkP_allN.1 h4 (μ - 1) (by rw [fbkP_pw2]; exact hlt))
    have hne := fbkP_notBeq hk'
    have e : Nat.succ (μ - 1) = μ := by omega
    rw [e] at hne
    exact ⟨k, hk, hne⟩

theorem fbkP_nIf_beq (s a b : Nat) :
    Bool.rec (motive := fun _ => Nat) b a (Nat.beq s (nat_lit 0)) = if s = 0 then a else b := by
  by_cases h : s = 0
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]
    have hb : Nat.beq s (nat_lit 0) = false := by
      cases hb : Nat.beq s (nat_lit 0)
      · rfl
      · exact absurd (fbkP_beq.1 hb) h
    rw [hb]

theorem fbkP_bit {X i : Nat} : bit X i = true ↔ X.testBit i = true := by
  change Nat.beq ((X >>> i) &&& 1) 1 = true ↔ _
  rw [fbkP_beq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_iff]

theorem fbkP_mask (CM R n b : Nat) (hb : b < n) : ∀ r, (∀ j < r, bit (fget CM (gI R j) n) b = true) →
    bit (Nat.rec (motive := fun _ => Nat) (Nat.sub (pw2 n) (nat_lit 1))
      (fun j ih => Nat.land (fget CM (gI R j) n) ih) r) b = true
  | 0, _ => by
    have e : Nat.sub (pw2 n) (nat_lit 1) = 2 ^ n - 1 := by
      rw [fbkP_pw2]
      rfl
    have h0 : bit (Nat.sub (pw2 n) (nat_lit 1)) b = true := by
      rw [e, fbkP_bit, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
      exact hb
    exact h0
  | r + 1, h => by
    have ih := fbkP_mask CM R n b hb r fun j hj => h j (Nat.lt_succ_of_lt hj)
    have hr := h r (Nat.lt_succ_self r)
    have hs : bit (Nat.land (fget CM (gI R r) n) (Nat.rec (motive := fun _ => Nat)
        (Nat.sub (pw2 n) (nat_lit 1)) (fun j ih => Nat.land (fget CM (gI R j) n) ih) r)) b = true := by
      rw [fbkP_bit] at ih hr ⊢
      change Nat.testBit (fget CM (gI R r) n &&& Nat.rec (motive := fun _ => Nat)
        (Nat.sub (pw2 n) (nat_lit 1)) (fun j ih => Nat.land (fget CM (gI R j) n) ih) r) b = true
      rw [Nat.testBit_and, ih, hr]
      rfl
    exact hs

theorem fbkP_walk {IV RG BP nB nE nR R r Cm : Nat} {rec : Nat → Nat} : ∀ (f b : Nat) (l : List Item),
    walk IV RG BP nB nE nR rec R r Cm f b l = true → ∀ c, b ≤ c → c < b + f → bit Cm c = true →
      ∃ it ∈ l, itemOK IV RG BP nB nE nR rec R r (ivc IV c) it = true
  | 0, b, l, _, c, hbc, hcf, _ => absurd hcf (by omega)
  | f + 1, b, l, h, c, hbc, hcf, hc => by
    cases hb : bit Cm b
    · have hw := fbkP_bIfF h hb
      by_cases e : c = b
      · rw [e, hb] at hc
        exact absurd hc Bool.false_ne_true
      · exact fbkP_walk f (b + 1) l hw c (by omega) (by omega) hc
    · have hw := fbkP_bIfT h hb
      cases l with
      | nil => exact absurd hw Bool.false_ne_true
      | cons it rest =>
        obtain ⟨ha, hr⟩ := fbkP_bAnd hw
        by_cases e : c = b
        · rw [fbkP_strictK] at ha
          rw [e]
          exact ⟨it, List.mem_cons_self .., ha⟩
        · obtain ⟨it', hit', h'⟩ := fbkP_walk f (b + 1) rest hr c (by omega) (by omega) hc
          exact ⟨it', List.mem_cons_of_mem _ hit', h'⟩

theorem srcOK_spec {IV RG CM BP nB nE nR n s : Nat} {rec : Nat → Nat} {items : List Item}
    (h : srcOK IV RG CM BP nB nE nR n rec s items = true) :
    s ≤ nR ∧ ∀ b < n,
      (∀ j < rk (if s = 0 then 0 else fget RG (s - 1) 56),
        bit (fget CM (gI (if s = 0 then 0 else fget RG (s - 1) 56) j) n) b = true) →
      ∃ it ∈ items, itemOK IV RG BP nB nE nR rec (if s = 0 then 0 else fget RG (s - 1) 56)
        (rk (if s = 0 then 0 else fget RG (s - 1) 56)) (ivc IV b) it = true := by
  obtain ⟨h1, h2⟩ := fbkP_bAnd h
  simp only [fbkP_strictK, fbkP_nIf_beq] at h2
  refine ⟨fbkP_ble.1 h1, fun b hb hall => ?_⟩
  exact fbkP_walk n 0 items h2 b (Nat.zero_le b) (by omega) (fbkP_mask CM _ n b hb _ hall)

theorem itemOK_spec {IV RG BP nB nE nR R r x : Nat} {rec : Nat → Nat} {it : Item}
    (h : itemOK IV RG BP nB nE nR rec R r x it = true) :
    (it.1 = 0 ∧ it.2.1 < 2 ^ r ∧ ∀ k < nB, ap x (bp BP k) = pA IV R it.2.1 (bp BP k)) ∨
      (0 < it.1 ∧ it.1 ≤ nR ∧ it.2.1 < nE ∧
        pairK IV BP nB R r x (fget RG (it.1 - 1) 56) (valF 120 (rec it.2.1)) it.2.2.1
          it.2.2.2.1 it.2.2.2.2 = true) := by
  unfold itemOK at h
  cases h0 : Nat.beq it.1 0
  · obtain ⟨h1, h2⟩ := fbkP_bAnd (fbkP_bIfF h h0)
    obtain ⟨h2, h3⟩ := fbkP_bAnd h2
    simp only [fbkP_strictK] at h3
    refine Or.inr ⟨Nat.pos_of_ne_zero fun he => ?_, fbkP_ble.1 h1, fbkP_blt.1 h2, h3⟩
    rw [he] at h0
    exact Bool.noConfusion h0
  · obtain ⟨h1, h2⟩ := fbkP_bAnd (fbkP_bIfT h h0)
    have hlt := fbkP_blt.1 h1
    rw [fbkP_pw2] at hlt
    exact Or.inl ⟨fbkP_beq.1 h0, hlt, fun k hk => fbkP_beq.1 (fbkP_allN.1 h2 k hk)⟩

theorem pairK_spec {IV BP nB R r x R' G cp mp sp : Nat}
    (h : pairK IV BP nB R r x R' G cp mp sp = true) :
    rk R' = r + 1 ∧ (∀ k < nB, ap G (fget cp k 5) = bp BP k) ∧
      (∀ i < r + 1, fget mp i 6 < 2 ^ (r + 1) ∧ ∀ k < nB,
        ap G (ap (if i < r then ivc IV (gI R i) else x) (fget cp k 5)) =
          pA IV R' (fget mp i 6) (bp BP k)) ∧
      ∀ i < r + 1, xorSel mp (fget sp i 6) (r + 1) = 2 ^ i := by
  obtain ⟨h1, h2⟩ := fbkP_bAnd h
  obtain ⟨h2, h3⟩ := fbkP_bAnd h2
  obtain ⟨h3, h4⟩ := fbkP_bAnd h3
  refine ⟨fbkP_beq.1 h1, fun k hk => fbkP_beq.1 (fbkP_allN.1 h2 k hk), fun i hi => ?_,
    fun i hi => ?_⟩
  · have hi' := fbkP_allN.1 h3 i hi
    simp only [fbkP_strictK, fbkP_nIf_blt] at hi'
    obtain ⟨ha, hb⟩ := fbkP_bAnd hi'
    have hlt := fbkP_blt.1 ha
    rw [fbkP_pw2] at hlt
    exact ⟨hlt, fun k hk => fbkP_beq.1 (fbkP_allN.1 hb k hk)⟩
  · have hx := fbkP_beq.1 (fbkP_allN.1 h4 i hi)
    rw [fbkP_pw2] at hx
    exact hx

end CFSG.KC.FixBoundK.Pair

end
