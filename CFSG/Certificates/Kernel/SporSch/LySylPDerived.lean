module

public import CFSG.Certificates.Kernel.SporSch.LySylDefs
import CFSG.Certificates.Kernel.Spor.PK.Basic
import CFSG.Certificates.Kernel.SporSch.LyLoop
public import CFSG.Sporadic.Schreier.LyCheckSylow

public section

namespace CFSG.KS.SporSch.LySylP.Derived

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.SporSch.LyM CFSG.Sporadic.LySchreier.Native
open CFSG.KS.SporSch.LySyl

private theorem b8_eq (x j : Nat) : b8 x j = x / 2 ^ (8 * j) % 256 := by
  show x >>> (Nat.mul 8 j) &&& 255 = _
  rw [Nat.shiftRight_eq_div_pow, show (255 : Nat) = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

private theorem anyN_iff {m : Nat} {f : Nat → Bool} :
    CFSG.KS.SporSch.anyN m f = true ↔ ∃ i < m, f i = true := by
  unfold CFSG.KS.SporSch.anyN
  simp only [CFSG.KS.PK.bIf_eq]
  by_cases h : allN m (fun i => if f i = true then false else true) = true
  · rw [if_pos h]
    have h' := CFSG.KS.PK.allN_iff.1 h
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro i hi hf
    have := h' i hi
    rw [if_pos hf] at this
    exact Bool.false_ne_true this
  · rw [if_neg h]
    simp only [true_iff]
    rw [CFSG.KS.PK.allN_iff] at h
    simp only [not_forall] at h
    obtain ⟨i, hi, hf⟩ := h
    refine ⟨i, hi, ?_⟩
    cases e : f i
    · rw [e] at hf
      exact absurd rfl hf
    · rfl

private theorem foldl_ext' {α β : Type} (f g : α → β → α) :
    ∀ (l : List β) (s : α), (∀ s, ∀ b ∈ l, f s b = g s b) → l.foldl f s = l.foldl g s
  | [], _, _ => rfl
  | b :: l, s, h => by
    rw [List.foldl_cons, List.foldl_cons, h s b List.mem_cons_self]
    exact foldl_ext' f g l _ fun s b hb => h s b (List.mem_cons_of_mem _ hb)

private theorem foldl_ofFn {α β : Type} (F : α → β → α) (g : Nat → β) :
    ∀ (m : Nat) (s : α), (Array.ofFn (n := m) fun t => g t.val).foldl F s =
      (List.range m).foldl (fun s t => F s (g t)) s
  | 0, s => by simp
  | m + 1, s => by
    rw [← CFSG.KS.SporSch.LyLoop.ofFn_push, Array.foldl_push, foldl_ofFn F g m s, List.range_succ,
      List.foldl_append]
    rfl

private theorem prefix_ne_zero (f : Nat → Nat → Nat) (hf : ∀ t, f t 0 = 0) (m s : Nat)
    (h : (List.range m).foldl (fun s t => f t s) s ≠ 0) :
    ∀ t ≤ m, (List.range t).foldl (fun s t => f t s) s ≠ 0 := by
  have hz : ∀ (g : Nat → Nat) (l : List Nat), l.foldl (fun s t => f (g t) s) 0 = 0 := by
    intro g l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.foldl_cons, hf, ih]
  intro t ht h0
  apply h
  rw [show m = t + (m - t) by omega, List.range_add, List.foldl_append, h0, List.foldl_map]
  exact hz (t + ·) _

private theorem tm_eq {MT : Nat → Nat} {n i j : Nat} (hi : i < n) (hj : j < n) :
    tm (TBL MT n) i j = tmK MT i j := by
  unfold tm TBL
  rw [CFSG.KS.SporSch.LyLoop.ofFn_getP (fun i => Array.ofFn (n := n) fun j => tmK MT i j.val) hi,
    CFSG.KS.SporSch.LyLoop.ofFn_getP (fun j => tmK MT i j) hj]

private theorem ivOK_spec {MT : Nat → Nat} {IV n i : Nat} (h : ivOK MT IV n i = true) :
    tinvK IV i < n ∧ tmK MT i (tinvK IV i) = 0 ∧ ∀ j < tinvK IV i, tmK MT i j ≠ 0 := by
  unfold ivOK at h
  rw [CFSG.KS.PK.strictB_eq] at h
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    CFSG.KS.PK.allN_iff, Bool.not_eq_true'] at h
  refine ⟨h.1, h.2.1, fun j hj e => ?_⟩
  have := h.2.2 j hj
  rw [e] at this
  exact Bool.noConfusion this

private theorem tinv_eq {MT : Nat → Nat} {IV n i : Nat} (hiv : ivOK MT IV n i = true) (hi : i < n) :
    tinv (TBL MT n) n i = tinvK IV i := by
  obtain ⟨h1, h2, h3⟩ := ivOK_spec hiv
  unfold tinv
  have e : (List.range n).find? (fun j => tm (TBL MT n) i j == 0) = some (tinvK IV i) := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, List.mem_range.2 h1, ?_⟩
    · rw [tm_eq hi h1, h2]
      rfl
    · intro j hj
      rw [tm_eq hi (by omega)]
      simpa using h3 j hj
  rw [e]
  rfl

private theorem tcommK_lt {MT : Nat → Nat} {IV n a b : Nat} (hiv : ∀ i < n, ivOK MT IV n i = true)
    (hr : ∀ i < n, ∀ j < n, tmK MT i j < n) (ha : a < n) (hb : b < n) : tcommK MT IV a b < n :=
  hr _ (hr _ (hr a ha b hb) _ (ivOK_spec (hiv a ha)).1) _ (ivOK_spec (hiv b hb)).1

private theorem tcomm_eq {MT : Nat → Nat} {IV n a b : Nat} (hiv : ∀ i < n, ivOK MT IV n i = true)
    (hr : ∀ i < n, ∀ j < n, tmK MT i j < n) (ha : a < n) (hb : b < n) :
    tcomm (TBL MT n) n a b = tcommK MT IV a b := by
  have ia := ivOK_spec (hiv a ha)
  have ib := ivOK_spec (hiv b hb)
  unfold tcomm tcommK
  rw [tinv_eq (hiv a ha) ha, tinv_eq (hiv b hb) hb, tm_eq ha hb, tm_eq (hr a ha b hb) ia.1,
    tm_eq (hr _ (hr a ha b hb) _ ia.1) ib.1]

private noncomputable def enc (c a b : Nat) : Nat :=
  Nat.lor c (Nat.lor (Nat.shiftLeft a (nat_lit 8)) (Nat.shiftLeft b (nat_lit 16)))

private theorem enc_eq {c a b : Nat} (hc : c < 256) (ha : a < 256) :
    enc c a b = c + 256 * a + 65536 * b := by
  show c ||| (a <<< 8 ||| b <<< 16) = _
  rw [show b <<< 16 = (b <<< 8) <<< 8 from Nat.shiftLeft_add b 8 8, ← Nat.shiftLeft_or_distrib,
    Nat.or_comm a, ← Nat.shiftLeft_add_eq_or_of_lt (show a < 2 ^ 8 from ha), Nat.or_comm c,
    ← Nat.shiftLeft_add_eq_or_of_lt (show c < 2 ^ 8 from hc)]
  simp only [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 from rfl]
  omega

private theorem dec_enc {c a b : Nat} (hc : c < 256) (ha : a < 256) (hb : b < 256) :
    b8 (enc c a b) 0 = c ∧ b8 (enc c a b) 1 = a ∧ b8 (enc c a b) 2 = b := by
  rw [b8_eq, b8_eq, b8_eq, enc_eq hc ha]
  simp only [show (2 : Nat) ^ (8 * 0) = 1 from rfl, show (2 : Nat) ^ (8 * 1) = 256 from rfl,
    show (2 : Nat) ^ (8 * 2) = 65536 from rfl]
  omega

private noncomputable def cstep (MT : Nat → Nat) (IV n : Nat) (cs : Array (Nat × Nat × Nat))
    (q : Nat) : Array (Nat × Nat × Nat) :=
  if (!cs.any fun t => t.1 == tcommK MT IV (q / n) (q % n)) = true then
    cs.push (tcommK MT IV (q / n) (q % n), q / n, q % n) else cs

private noncomputable def CS (MT : Nat → Nat) (IV n q : Nat) : Array (Nat × Nat × Nat) :=
  (List.range q).foldl (cstep MT IV n) #[]

private theorem CS_succ (MT : Nat → Nat) (IV n q : Nat) :
    CS MT IV n (q + 1) = cstep MT IV n (CS MT IV n q) q := by
  unfold CS
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem any_fst_iff (cs : Array (Nat × Nat × Nat)) (c : Nat) :
    (cs.any fun t => t.1 == c) = true ↔ ∃ e ∈ cs.toList, e.1 = c := by
  rw [← Array.any_toList, List.any_eq_true]
  simp

private theorem CS_props {MT : Nat → Nat} {IV n : Nat} (hiv : ∀ i < n, ivOK MT IV n i = true)
    (hr : ∀ i < n, ∀ j < n, tmK MT i j < n) : ∀ q ≤ n * n,
    (∀ e ∈ (CS MT IV n q).toList, e.1 < n ∧ e.2.1 < n ∧ e.2.2 < n) ∧
      ((CS MT IV n q).toList.map Prod.fst).Nodup
  | 0, _ => by simp [CS]
  | q + 1, hq => by
    obtain ⟨h1, h2⟩ := CS_props hiv hr q (by omega)
    have hn : 0 < n := Nat.pos_of_ne_zero fun e => by subst e; simp at hq
    have ha : q / n < n := Nat.div_lt_of_lt_mul (by omega)
    have hb : q % n < n := Nat.mod_lt _ hn
    rw [CS_succ]
    unfold cstep
    split
    · rename_i hnot
      have hnot' : ¬ ∃ e ∈ (CS MT IV n q).toList, e.1 = tcommK MT IV (q / n) (q % n) := by
        rw [← any_fst_iff]
        simpa using hnot
      simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
      refine ⟨?_, ?_⟩
      · intro e he
        rcases List.mem_append.1 he with he | he
        · exact h1 e he
        · rw [List.mem_singleton] at he
          subst he
          exact ⟨tcommK_lt hiv hr ha hb, ha, hb⟩
      · rw [List.nodup_append]
        refine ⟨h2, List.nodup_singleton _, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy hxy
        obtain ⟨e, he, hee⟩ := List.mem_map.1 hx
        exact hnot' ⟨e, he, hee⟩
    · exact ⟨h1, h2⟩

private theorem CS_size_le {MT : Nat → Nat} {IV n : Nat} (hiv : ∀ i < n, ivOK MT IV n i = true)
    (hr : ∀ i < n, ∀ j < n, tmK MT i j < n) {q : Nat} (hq : q ≤ n * n) :
    (CS MT IV n q).size ≤ n := by
  obtain ⟨h1, h2⟩ := CS_props hiv hr q hq
  have hsub : (CS MT IV n q).toList.map Prod.fst ⊆ List.range n := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (h1 e he).1
  have := (h2.subperm hsub).length_le
  simpa using this

private def Inv (MT : Nat → Nat) (IV n : Nat) (CM : Nat → Nat) (q cnt mask : Nat) : Prop :=
  cnt = (CS MT IV n q).size ∧
    (∀ t < cnt, CM t = enc ((CS MT IV n q)[t]!).1 ((CS MT IV n q)[t]!).2.1
      ((CS MT IV n q)[t]!).2.2) ∧
    ∀ x, mask.testBit x = true ↔ ∃ e ∈ (CS MT IV n q).toList, e.1 = x

private theorem commsK_succ (MT : Nat → Nat) (IV n : Nat) (CM : Nat → Nat) (len q cnt mask : Nat) :
    commsK MT IV n CM (len + 1) q cnt mask =
      if Nat.beq cnt 65535 = true then 65535 else
      if hasBit mask (tcommK MT IV (q / n) (q % n)) = true then
        commsK MT IV n CM len (q + 1) cnt mask else
      if Nat.beq (CM cnt) (enc (tcommK MT IV (q / n) (q % n)) (q / n) (q % n)) = true then
        commsK MT IV n CM len (q + 1) (cnt + 1)
          (Nat.lor mask (Nat.shiftLeft 1 (tcommK MT IV (q / n) (q % n))))
      else 65535 := by
  have e : commsK MT IV n CM (len + 1) q cnt mask = strictN (Nat.div q n) (fun a =>
      strictN (Nat.mod q n) (fun b => strictN (tcommK MT IV a b) (fun c =>
        strictN (Nat.succ q) (fun q' =>
          nIf(Nat.beq cnt (nat_lit 65535), nat_lit 65535,
          nIf(hasBit mask c, commsK MT IV n CM len q' cnt mask,
            nIf(Nat.beq (CM cnt) (Nat.lor c (Nat.lor (Nat.shiftLeft a (nat_lit 8))
                (Nat.shiftLeft b (nat_lit 16)))),
              strictN (Nat.succ cnt) (fun cnt' =>
                strictN (Nat.lor mask (Nat.shiftLeft (nat_lit 1) c)) (fun mask' =>
                  commsK MT IV n CM len q' cnt' mask')),
              nat_lit 65535))))))) := rfl
  rw [e]
  simp only [CFSG.KS.PK.strictN_eq, CFSG.KS.PK.nIf_eq]
  rfl

private theorem commsK_fail (MT : Nat → Nat) (IV n : Nat) (CM : Nat → Nat) (len q : Nat) :
    commsK MT IV n CM len q 65535 0 = 65535 := by
  cases len with
  | zero => rfl
  | succ len =>
    rw [commsK_succ]
    rfl

private theorem scan_sound {MT : Nat → Nat} {IV n : Nat} {CM : Nat → Nat} (hn : n ≤ 256)
    (hiv : ∀ i < n, ivOK MT IV n i = true) (hr : ∀ i < n, ∀ j < n, tmK MT i j < n) :
    ∀ len q cnt mask, q + len ≤ n * n → Inv MT IV n CM q cnt mask →
      commsK MT IV n CM len q cnt mask = 65535 ∨
      ∃ cnt' mask', commsK MT IV n CM len q cnt mask = cnt' + mask' * 65536 ∧
        Inv MT IV n CM (q + len) cnt' mask'
  | 0, q, cnt, mask, _, hI => by
    right
    refine ⟨cnt, mask, ?_, hI⟩
    show Nat.add cnt (Nat.shiftLeft mask 16) = _
    rw [show Nat.shiftLeft mask 16 = mask * 2 ^ 16 from Nat.shiftLeft_eq mask 16]
    rfl
  | len + 1, q, cnt, mask, hq, hI => by
    obtain ⟨hc, hCM, hM⟩ := hI
    have hqn : q < n * n := by omega
    have hn0 : 0 < n := Nat.pos_of_ne_zero fun e => by subst e; simp at hqn
    have ha : q / n < n := Nat.div_lt_of_lt_mul hqn
    have hb : q % n < n := Nat.mod_lt _ hn0
    have hcn := tcommK_lt hiv hr ha hb
    have hsz := CS_size_le hiv hr (q := q) (by omega)
    rw [commsK_succ]
    have h1 : Nat.beq cnt 65535 = false := by
      cases h : Nat.beq cnt 65535
      · rfl
      · have := Nat.eq_of_beq_eq_true h
        omega
    rw [h1, if_neg Bool.false_ne_true]
    by_cases hbit : hasBit mask (tcommK MT IV (q / n) (q % n)) = true
    · rw [if_pos hbit]
      rw [CFSG.KS.PK.hasBit_eq] at hbit
      have hmem := (hM _).1 hbit
      have hstep : CS MT IV n (q + 1) = CS MT IV n q := by
        rw [CS_succ]
        unfold cstep
        rw [if_neg]
        rw [← any_fst_iff] at hmem
        simp [hmem]
      have := scan_sound hn hiv hr len (q + 1) cnt mask (by omega)
        ⟨by rw [hstep]; exact hc, by rw [hstep]; exact hCM, by rw [hstep]; exact hM⟩
      rwa [show q + 1 + len = q + (len + 1) by omega] at this
    · rw [if_neg hbit]
      by_cases hen : Nat.beq (CM cnt) (enc (tcommK MT IV (q / n) (q % n)) (q / n) (q % n)) = true
      · rw [if_pos hen]
        rw [CFSG.KS.PK.hasBit_eq] at hbit
        have hnot : ¬ ∃ e ∈ (CS MT IV n q).toList, e.1 = tcommK MT IV (q / n) (q % n) :=
          fun h => hbit ((hM _).2 h)
        have hstep : CS MT IV n (q + 1) =
            (CS MT IV n q).push (tcommK MT IV (q / n) (q % n), q / n, q % n) := by
          rw [CS_succ]
          unfold cstep
          rw [if_pos]
          rw [← any_fst_iff] at hnot
          simpa using hnot
        have hI' : Inv MT IV n CM (q + 1) (cnt + 1)
            (Nat.lor mask (Nat.shiftLeft 1 (tcommK MT IV (q / n) (q % n)))) := by
          refine ⟨?_, ?_, ?_⟩
          · rw [hstep, Array.size_push, hc]
          · intro t ht
            rw [hstep]
            rcases Nat.lt_or_ge t cnt with htc | htc
            · rw [getElem!_pos _ t (by rw [Array.size_push]; omega), Array.getElem_push_lt (by omega),
                ← getElem!_pos (CS MT IV n q) t (by omega)]
              exact hCM t htc
            · obtain rfl : t = cnt := by omega
              rw [getElem!_pos _ t (by rw [Array.size_push]; omega)]
              have hen' := Nat.eq_of_beq_eq_true hen
              rw [hc] at hen'
              simp only [hc, Array.getElem_push_eq]
              exact hen'
          · intro x
            rw [hstep, Array.toList_push]
            simp only [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, List.mem_append,
              List.mem_singleton]
            rw [show Nat.shiftLeft 1 (tcommK MT IV (q / n) (q % n)) =
              2 ^ tcommK MT IV (q / n) (q % n) from Nat.one_shiftLeft _, Nat.testBit_two_pow, hM x]
            constructor
            · rintro (⟨e, he, rfl⟩ | h)
              · exact ⟨e, Or.inl he, rfl⟩
              · exact ⟨_, Or.inr rfl, of_decide_eq_true h⟩
            · rintro ⟨e, he | rfl, rfl⟩
              · exact Or.inl ⟨e, he, rfl⟩
              · exact Or.inr (decide_eq_true rfl)
        have := scan_sound hn hiv hr len (q + 1) (cnt + 1) _ (by omega) hI'
        rwa [show q + 1 + len = q + (len + 1) by omega] at this
      · rw [if_neg hen]
        left
        rfl

private theorem slices_sound {n nS len : Nat} {MT CM ST : Nat → Nat} {IV : Nat} (hn : n ≤ 256)
    (hiv : ∀ i < n, ivOK MT IV n i = true) (hr : ∀ i < n, ∀ j < n, tmK MT i j < n)
    (hlen : nS * len = n * n) (hS0 : ST 0 = 0)
    (hslice : ∀ s < nS, commsK MT IV n CM len (Nat.mul s len) (Nat.land (ST s) 65535)
      (Nat.shiftRight (ST s) 16) = ST (Nat.succ s)) :
    ∀ s ≤ nS, ST s = 65535 ∨
      ∃ cnt mask, ST s = cnt + mask * 65536 ∧ Inv MT IV n CM (s * len) cnt mask
  | 0, _ => by
    right
    refine ⟨0, 0, by rw [hS0], ?_, ?_, ?_⟩
    · simp [CS]
    · intro t ht
      exact absurd ht (Nat.not_lt_zero t)
    · intro x
      simp [CS]
  | s + 1, hs => by
    have e := hslice s (by omega)
    rcases slices_sound hn hiv hr hlen hS0 hslice s (by omega) with h | ⟨cnt, mask, h, hI⟩
    · left
      rw [← e, h]
      exact commsK_fail MT IV n CM len _
    · have hcnt : cnt < 65536 := by
        have := CS_size_le hiv hr (q := s * len)
          (by rw [← hlen]; exact Nat.mul_le_mul_right _ (by omega))
        rw [hI.1]
        omega
      have d1 : Nat.land (ST s) 65535 = cnt := by
        rw [h, Nat.land_eq, show (65535 : Nat) = 2 ^ 16 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
        show (cnt + mask * 65536) % 65536 = cnt
        omega
      have d2 : Nat.shiftRight (ST s) 16 = mask := by
        rw [h]
        show (cnt + mask * 65536) >>> 16 = mask
        rw [Nat.shiftRight_eq_div_pow]
        show (cnt + mask * 65536) / 65536 = mask
        omega
      rw [d1, d2] at e
      change commsK MT IV n CM len (s * len) cnt mask = ST (s + 1) at e
      rcases scan_sound hn hiv hr len (s * len) cnt mask
          (by rw [← Nat.succ_mul, ← hlen]; exact Nat.mul_le_mul_right _ hs) hI with h' | ⟨c', m', h', hI'⟩
      · left
        rw [← e, h']
      · right
        refine ⟨c', m', by rw [← e, h'], ?_⟩
        rwa [Nat.succ_mul]

private noncomputable def stt (DT : Nat → Nat) (c : Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  (Array.ofFn (n := c) fun k => b8 (DT k.val) 0, Array.ofFn (n := c) fun k => b8 (DT k.val) 1,
    Array.ofFn (n := c) fun k => b8 (DT k.val) 2, Array.ofFn (n := c) fun k => b8 (DT k.val) 3)

private def tstep (T : Array (Array Nat)) (h : Nat)
    (s : Array Nat × Array Nat × Array Nat × Array Nat) (t : Nat × Nat × Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  if (!s.1.contains (tm T t.1 s.1[h]!)) = true then
    (s.1.push (tm T t.1 s.1[h]!), s.2.1.push h, s.2.2.1.push t.2.1, s.2.2.2.push t.2.2)
  else s

private def hstep (T : Array (Array Nat)) (cs : Array (Nat × Nat × Nat))
    (s : Array Nat × Array Nat × Array Nat × Array Nat) (h : Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  if h < s.1.size then cs.foldl (tstep T h) s else s

private def ccstep (T : Array (Array Nat)) (n : Nat) (cs : Array (Nat × Nat × Nat)) (a b : Nat) :
    Array (Nat × Nat × Nat) :=
  if (!cs.any fun t => t.1 == tcomm T n a b) = true then cs.push (tcomm T n a b, a, b) else cs

private def commsL (T : Array (Array Nat)) (n : Nat) : Array (Nat × Nat × Nat) :=
  (List.range n).foldl (fun cs a => (List.range n).foldl (fun cs b => ccstep T n cs a b) cs) #[]

private theorem ite_pure_yield {β : Type} (q : Prop) [Decidable q] (a b : β) :
    (if q then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if q then a else b)) := by
  split <;> rfl

private theorem derivedTree_eq (T : Array (Array Nat)) (n : Nat) :
    derivedTree T n = (List.range n).foldl (hstep T (commsL T n)) (#[0], #[0], #[0], #[0]) := by
  unfold derivedTree
  have h1 : ∀ a b : Nat, [a:b].size = b - a := fun a b => by simp [Std.Legacy.Range.size]
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yield,
    List.forIn_pure_yield_eq_foldl, Array.forIn_pure_yield_eq_foldl, pure_bind, h1, Nat.sub_zero,
    ← List.range_eq_range']
  rfl

private theorem nest {α : Type} (f : α → Nat → α) (n : Nat) : ∀ (N : Nat) (s : α),
    (List.range (N * n)).foldl f s =
      (List.range N).foldl (fun s a => (List.range n).foldl (fun s b => f s (a * n + b)) s) s
  | 0, s => by simp
  | N + 1, s => by
    rw [Nat.succ_mul, List.range_add, List.foldl_append, nest f n N s, List.foldl_map,
      List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem commsL_eq {MT : Nat → Nat} {IV n : Nat} (hiv : ∀ i < n, ivOK MT IV n i = true)
    (hr : ∀ i < n, ∀ j < n, tmK MT i j < n) : commsL (TBL MT n) n = CS MT IV n (n * n) := by
  unfold commsL CS
  rw [nest]
  apply foldl_ext'
  intro s a ha
  apply foldl_ext'
  intro s b hb
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  have hn0 : 0 < n := by omega
  have e1 : (a * n + b) / n = a := by
    rw [Nat.mul_comm, Nat.mul_add_div hn0, Nat.div_eq_of_lt hb', Nat.add_zero]
  have e2 : (a * n + b) % n = b := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
  unfold cstep ccstep
  rw [e1, e2, tcomm_eq hiv hr ha' hb']

private theorem comms_final {n nC nS len : Nat} {MT CM ST : Nat → Nat} {IV : Nat} (hn : n ≤ 256)
    (hiv : ∀ i < n, ivOK MT IV n i = true) (hr : ∀ i < n, ∀ j < n, tmK MT i j < n)
    (hlen : nS * len = n * n) (hS0 : ST 0 = 0)
    (hslice : ∀ s < nS, commsK MT IV n CM len (Nat.mul s len) (Nat.land (ST s) 65535)
      (Nat.shiftRight (ST s) 16) = ST (Nat.succ s))
    (hnC : Nat.land (ST nS) 65535 = nC) (hnC' : nC < 65535) :
    CS MT IV n (n * n) =
        (Array.ofFn (n := nC) fun t => (b8 (CM t.val) 0, b8 (CM t.val) 1, b8 (CM t.val) 2)) ∧
      ∀ t < nC, b8 (CM t) 0 < n := by
  rcases slices_sound hn hiv hr hlen hS0 hslice nS le_rfl with h | ⟨cnt, mask, h, hI⟩
  · rw [h] at hnC
    have : nC = 65535 := by rw [← hnC]; rfl
    omega
  · rw [hlen] at hI
    obtain ⟨hc, hCM, -⟩ := hI
    have hsz := CS_size_le hiv hr (le_refl (n * n))
    have hcnt : cnt = nC := by
      rw [← hnC, h, Nat.land_eq, show (65535 : Nat) = 2 ^ 16 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      show cnt = (cnt + mask * 65536) % 65536
      omega
    subst hcnt
    obtain ⟨hP, -⟩ := CS_props hiv hr (n * n) le_rfl
    have hent : ∀ t < cnt, (CS MT IV n (n * n))[t]! = (b8 (CM t) 0, b8 (CM t) 1, b8 (CM t) 2) ∧
        b8 (CM t) 0 < n := by
      intro t ht
      have hmem : (CS MT IV n (n * n))[t]! ∈ (CS MT IV n (n * n)).toList := by
        rw [getElem!_pos _ t (by omega)]
        exact Array.getElem_mem_toList _
      obtain ⟨p1, p2, p3⟩ := hP _ hmem
      obtain ⟨d1, d2, d3⟩ := dec_enc (show ((CS MT IV n (n * n))[t]!).1 < 256 by omega)
        (show ((CS MT IV n (n * n))[t]!).2.1 < 256 by omega)
        (show ((CS MT IV n (n * n))[t]!).2.2 < 256 by omega)
      rw [hCM t ht, d1, d2, d3]
      exact ⟨rfl, p1⟩
    refine ⟨?_, fun t ht => (hent t ht).2⟩
    apply Array.ext
    · rw [Array.size_ofFn, ← hc]
    · intro i h1 h2
      rw [Array.getElem_ofFn, ← (hent i (by omega)).1, getElem!_pos _ i h1]

private noncomputable def istep (MT CM DT : Nat → Nat) (nC nD h t cur : Nat) : Nat :=
  nIf(Nat.beq cur (nat_lit 0), nat_lit 0,
    strictN (tmK MT (b8 (CM t) 0) (b8 (DT h) 0)) (fun y =>
      nIf(CFSG.KS.SporSch.anyN cur (fun i => Nat.beq (b8 (DT i) 0) y), cur,
        nIf(bAnd(Nat.blt cur nD, bAnd(Nat.beq (b8 (DT cur) 0) y, bAnd(Nat.beq (b8 (DT cur) 1) h,
            bAnd(Nat.beq (b8 (DT cur) 2) (b8 (CM t) 1), Nat.beq (b8 (DT cur) 3) (b8 (CM t) 2))))),
          Nat.succ cur, nat_lit 0))))

private theorem dtHead_eq (MT CM DT : Nat → Nat) (nC nD h cur : Nat) :
    dtHead MT CM DT nC nD h cur =
      (List.range nC).foldl (fun s t => istep MT CM DT nC nD h t s) cur :=
  CFSG.KS.PK.foldUp_eq nC (fun t cur => istep MT CM DT nC nD h t cur) cur

private theorem istep_spec {MT CM DT : Nat → Nat} {nC nD h t cur : Nat} (h0 : cur ≠ 0)
    (hne : istep MT CM DT nC nD h t cur ≠ 0) :
    ((∃ i < cur, b8 (DT i) 0 = tmK MT (b8 (CM t) 0) (b8 (DT h) 0)) ∧
        istep MT CM DT nC nD h t cur = cur) ∨
      ((¬ ∃ i < cur, b8 (DT i) 0 = tmK MT (b8 (CM t) 0) (b8 (DT h) 0)) ∧
        istep MT CM DT nC nD h t cur = cur + 1 ∧ cur < nD ∧
        b8 (DT cur) 0 = tmK MT (b8 (CM t) 0) (b8 (DT h) 0) ∧ b8 (DT cur) 1 = h ∧
        b8 (DT cur) 2 = b8 (CM t) 1 ∧ b8 (DT cur) 3 = b8 (CM t) 2) := by
  have hb0 : Nat.beq cur 0 = false := by
    cases e : Nat.beq cur 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h0
  unfold istep at hne ⊢
  rw [hb0] at hne ⊢
  simp only [CFSG.KS.PK.strictN_eq, CFSG.KS.PK.nIf_eq, CFSG.KS.PK.bAnd_eq, Bool.false_eq_true,
    if_false] at hne ⊢
  by_cases ha : CFSG.KS.SporSch.anyN cur
      (fun i => Nat.beq (b8 (DT i) 0) (tmK MT (b8 (CM t) 0) (b8 (DT h) 0))) = true
  · left
    rw [if_pos ha]
    refine ⟨?_, rfl⟩
    obtain ⟨i, hi, e⟩ := anyN_iff.1 ha
    exact ⟨i, hi, Nat.eq_of_beq_eq_true e⟩
  · right
    rw [if_neg ha] at hne ⊢
    have hna : ¬ ∃ i < cur, b8 (DT i) 0 = tmK MT (b8 (CM t) 0) (b8 (DT h) 0) :=
      fun ⟨i, hi, e⟩ => ha (anyN_iff.2 ⟨i, hi, by rw [e]; exact Nat.beq_refl _⟩)
    by_cases hc : (Nat.blt cur nD && (Nat.beq (b8 (DT cur) 0) (tmK MT (b8 (CM t) 0) (b8 (DT h) 0)) &&
        (Nat.beq (b8 (DT cur) 1) h && (Nat.beq (b8 (DT cur) 2) (b8 (CM t) 1) &&
          Nat.beq (b8 (DT cur) 3) (b8 (CM t) 2))))) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
      exact ⟨hna, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
    · rw [if_neg hc] at hne
      exact absurd rfl hne

private theorem tstep_sound {MT CM DT : Nat → Nat} {n nC nD h t cur : Nat}
    (hr : ∀ i < n, ∀ j < n, tmK MT i j < n) (hct : b8 (CM t) 0 < n) (h0 : cur ≠ 0)
    (hh : h < cur) (hB : ∀ k < cur, b8 (DT k) 0 < n) (hne : istep MT CM DT nC nD h t cur ≠ 0) :
    tstep (TBL MT n) h (stt DT cur) (b8 (CM t) 0, b8 (CM t) 1, b8 (CM t) 2) =
        stt DT (istep MT CM DT nC nD h t cur) ∧ h < istep MT CM DT nC nD h t cur ∧
      ∀ k < istep MT CM DT nC nD h t cur, b8 (DT k) 0 < n := by
  have hd : (stt DT cur).1[h]! = b8 (DT h) 0 :=
    CFSG.KS.SporSch.LyLoop.ofFn_getP (fun k => b8 (DT k) 0) hh
  have hy : tm (TBL MT n) (b8 (CM t) 0) (b8 (DT h) 0) = tmK MT (b8 (CM t) 0) (b8 (DT h) 0) :=
    tm_eq hct (hB h hh)
  have hcont : ∀ y, (stt DT cur).1.contains y = true ↔ ∃ i < cur, b8 (DT i) 0 = y := by
    intro y
    unfold stt
    rw [Array.contains_iff_mem, Array.mem_ofFn]
    exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.isLt, hi⟩, fun ⟨i, hi, e⟩ => ⟨⟨i, hi⟩, e⟩⟩
  unfold tstep
  simp only [hd, hy]
  rcases istep_spec h0 hne with ⟨hex, heq⟩ | ⟨hnex, heq, -, f0, f1, f2, f3⟩
  · have hc := (hcont _).2 hex
    rw [if_neg (by rw [hc]; exact Bool.false_ne_true), heq]
    exact ⟨rfl, hh, hB⟩
  · have hc : (stt DT cur).1.contains (tmK MT (b8 (CM t) 0) (b8 (DT h) 0)) = false := by
      cases e : (stt DT cur).1.contains (tmK MT (b8 (CM t) 0) (b8 (DT h) 0))
      · rfl
      · exact absurd ((hcont _).1 e) hnex
    rw [if_pos (by rw [hc]; rfl), heq]
    refine ⟨?_, by omega, ?_⟩
    · have p0 : (Array.ofFn (n := cur) fun k => b8 (DT k.val) 0).push (b8 (DT cur) 0) =
          Array.ofFn (n := cur + 1) fun k => b8 (DT k.val) 0 :=
        CFSG.KS.SporSch.LyLoop.ofFn_push (fun k => b8 (DT k) 0) cur
      have p1 : (Array.ofFn (n := cur) fun k => b8 (DT k.val) 1).push (b8 (DT cur) 1) =
          Array.ofFn (n := cur + 1) fun k => b8 (DT k.val) 1 :=
        CFSG.KS.SporSch.LyLoop.ofFn_push (fun k => b8 (DT k) 1) cur
      have p2 : (Array.ofFn (n := cur) fun k => b8 (DT k.val) 2).push (b8 (DT cur) 2) =
          Array.ofFn (n := cur + 1) fun k => b8 (DT k.val) 2 :=
        CFSG.KS.SporSch.LyLoop.ofFn_push (fun k => b8 (DT k) 2) cur
      have p3 : (Array.ofFn (n := cur) fun k => b8 (DT k.val) 3).push (b8 (DT cur) 3) =
          Array.ofFn (n := cur + 1) fun k => b8 (DT k.val) 3 :=
        CFSG.KS.SporSch.LyLoop.ofFn_push (fun k => b8 (DT k) 3) cur
      rw [f0] at p0
      rw [f1] at p1
      rw [f2] at p2
      rw [f3] at p3
      unfold stt
      dsimp only
      rw [p0, p1, p2, p3]
    · intro k hk
      rcases Nat.lt_or_ge k cur with hk' | hk'
      · exact hB k hk'
      · obtain rfl : k = cur := by omega
        rw [f0]
        exact hr _ hct _ (hB h hh)

private theorem inner_sound {MT CM DT : Nat → Nat} {n nC nD h cur : Nat}
    (hr : ∀ i < n, ∀ j < n, tmK MT i j < n) (hc : ∀ t < nC, b8 (CM t) 0 < n)
    (h0 : cur ≠ 0) (hh : h < cur) (hB : ∀ k < cur, b8 (DT k) 0 < n)
    (hfin : dtHead MT CM DT nC nD h cur ≠ 0) :
    (Array.ofFn (n := nC) fun t => (b8 (CM t.val) 0, b8 (CM t.val) 1, b8 (CM t.val) 2)).foldl
        (tstep (TBL MT n) h) (stt DT cur) = stt DT (dtHead MT CM DT nC nD h cur) ∧
      ∀ k < dtHead MT CM DT nC nD h cur, b8 (DT k) 0 < n := by
  rw [foldl_ofFn (tstep (TBL MT n) h) (fun t => (b8 (CM t) 0, b8 (CM t) 1, b8 (CM t) 2)),
    dtHead_eq]
  rw [dtHead_eq] at hfin
  have hne := prefix_ne_zero (fun t s => istep MT CM DT nC nD h t s) (fun t => rfl) nC cur hfin
  have key : ∀ t ≤ nC,
      (List.range t).foldl (fun s t => tstep (TBL MT n) h s (b8 (CM t) 0, b8 (CM t) 1, b8 (CM t) 2))
          (stt DT cur) =
        stt DT ((List.range t).foldl (fun s t => istep MT CM DT nC nD h t s) cur) ∧
      h < (List.range t).foldl (fun s t => istep MT CM DT nC nD h t s) cur ∧
      ∀ k < (List.range t).foldl (fun s t => istep MT CM DT nC nD h t s) cur, b8 (DT k) 0 < n := by
    intro t
    induction t with
    | zero => intro _; exact ⟨rfl, hh, hB⟩
    | succ t ih =>
      intro ht
      obtain ⟨e1, e2, e3⟩ := ih (by omega)
      have hc0 := hne t (by omega)
      have hc1 := hne (t + 1) ht
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hc1
      rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_cons, List.foldl_nil, e1]
      exact tstep_sound hr (hc t (by omega)) hc0 e2 e3 hc1
  obtain ⟨k1, -, k3⟩ := key nC le_rfl
  exact ⟨k1, k3⟩

private noncomputable def ostep (MT CM DT : Nat → Nat) (nC nD h cur : Nat) : Nat :=
  nIf(Nat.blt h cur, dtHead MT CM DT nC nD h cur, cur)

private noncomputable def FH (MT CM DT : Nat → Nat) (nC nD h : Nat) : Nat :=
  (List.range h).foldl (fun s i => ostep MT CM DT nC nD i s) 1

private theorem FH_succ (MT CM DT : Nat → Nat) (nC nD h : Nat) :
    FH MT CM DT nC nD (h + 1) = ostep MT CM DT nC nD h (FH MT CM DT nC nD h) := by
  unfold FH
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem ostep_lt {MT CM DT : Nat → Nat} {nC nD h cur : Nat} (hlt : h < cur) :
    ostep MT CM DT nC nD h cur = dtHead MT CM DT nC nD h cur := by
  have e : Nat.blt h cur = true := by simpa using hlt
  unfold ostep
  rw [e]

private theorem ostep_ge {MT CM DT : Nat → Nat} {nC nD h cur : Nat} (hlt : ¬ h < cur) :
    ostep MT CM DT nC nD h cur = cur := by
  have e : Nat.blt h cur = false := by
    cases e : Nat.blt h cur
    · rfl
    · exact absurd (by simpa using e) hlt
  unfold ostep
  rw [e]

private theorem FH_ne {MT CM DT : Nat → Nat} {nC nD : Nat} (hdt : dtRun MT CM DT nC nD = nD) :
    nD ≠ 0 ∧ (∀ k, FH MT CM DT nC nD (nD + k) = nD) ∧ ∀ h, FH MT CM DT nC nD h ≠ 0 := by
  have hF : FH MT CM DT nC nD nD = nD := (CFSG.KS.PK.foldUp_eq _ _ _).symm.trans hdt
  have hnD : nD ≠ 0 := by
    intro e
    rw [e] at hF
    exact absurd hF (by unfold FH; simp)
  have hge : ∀ k, FH MT CM DT nC nD (nD + k) = nD := by
    intro k
    induction k with
    | zero => exact hF
    | succ k ih => rw [← Nat.add_assoc, FH_succ, ih, ostep_ge (by omega)]
  refine ⟨hnD, hge, fun h => ?_⟩
  rcases Nat.lt_or_ge h nD with hh | hh
  · have := prefix_ne_zero (fun t s => ostep MT CM DT nC nD t s)
      (fun t => ostep_ge (Nat.not_lt_zero t)) nD 1 (by rw [← hF] at hnD; exact hnD) h hh.le
    exact this
  · rw [show h = nD + (h - nD) by omega, hge]
    exact hnD

private theorem outer_sound {MT CM DT : Nat → Nat} {n nC nD : Nat}
    (hr : ∀ i < n, ∀ j < n, tmK MT i j < n) (hc : ∀ t < nC, b8 (CM t) 0 < n)
    (hn0 : 0 < n) (hDT0 : DT 0 = 0) (hFne : ∀ h, FH MT CM DT nC nD h ≠ 0) :
    ∀ h ≤ n, (List.range h).foldl (hstep (TBL MT n)
        (Array.ofFn (n := nC) fun t => (b8 (CM t.val) 0, b8 (CM t.val) 1, b8 (CM t.val) 2)))
        (#[0], #[0], #[0], #[0]) = stt DT (FH MT CM DT nC nD h) ∧
      ∀ k < FH MT CM DT nC nD h, b8 (DT k) 0 < n := by
  intro h
  induction h with
  | zero =>
    intro _
    have hb0 : ∀ j, b8 (DT 0) j = 0 := by
      intro j
      rw [hDT0, b8_eq]
      simp
    refine ⟨?_, ?_⟩
    · show _ = stt DT 1
      unfold stt
      simp [Array.ofFn_succ, hb0]
    · intro k hk
      have : k = 0 := by unfold FH at hk; simp at hk; omega
      subst this
      rw [hb0]
      exact hn0
  | succ h ih =>
    intro hh
    obtain ⟨e1, e2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, e1, FH_succ]
    have hs : (stt DT (FH MT CM DT nC nD h)).1.size = FH MT CM DT nC nD h := by
      unfold stt
      simp
    unfold hstep
    rw [hs]
    by_cases hlt : h < FH MT CM DT nC nD h
    · rw [if_pos hlt, ostep_lt hlt]
      refine inner_sound hr hc (hFne h) hlt e2 ?_
      rw [← ostep_lt hlt, ← FH_succ]
      exact hFne (h + 1)
    · rw [if_neg hlt, ostep_ge hlt]
      exact ⟨rfl, e2⟩

theorem derived_sound {n nC nD nS len : Nat} {MT CM DT ST : Nat → Nat} {IV : Nat}
    (hn : n ≤ 256) (hD : nD ≤ n) (hiv : ∀ i < n, ivOK MT IV n i = true)
    (hrows : ∀ i < n, Nat.blt (MT i) (Nat.shiftLeft 1 (Nat.mul 8 n)) = true ∧
      ∀ j < n, tmK MT i j < n)
    (hlen : nS * len = n * n) (hS0 : ST 0 = 0)
    (hslice : ∀ s < nS, commsK MT IV n CM len (Nat.mul s len) (Nat.land (ST s) 65535)
      (Nat.shiftRight (ST s) 16) = ST (Nat.succ s))
    (hnC : Nat.land (ST nS) 65535 = nC) (hnC' : nC < 65535) (hDT0 : DT 0 = 0)
    (hdt : dtRun MT CM DT nC nD = nD) :
    derivedTree (TBL MT n) n = (Array.ofFn (n := nD) fun k => b8 (DT k.val) 0,
      Array.ofFn (n := nD) fun k => b8 (DT k.val) 1, Array.ofFn (n := nD) fun k => b8 (DT k.val) 2,
      Array.ofFn (n := nD) fun k => b8 (DT k.val) 3) := by
  have hr : ∀ i < n, ∀ j < n, tmK MT i j < n := fun i hi => (hrows i hi).2
  obtain ⟨hG, hc⟩ := comms_final hn hiv hr hlen hS0 hslice hnC hnC'
  obtain ⟨hnD, hge, hFne⟩ := FH_ne hdt
  rw [derivedTree_eq, commsL_eq hiv hr, hG,
    (outer_sound hr hc (by omega) hDT0 hFne n le_rfl).1, show n = nD + (n - nD) by omega, hge]
  rfl

end CFSG.KS.SporSch.LySylP.Derived

end
