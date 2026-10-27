module

public import Certificates.Data.Kernel.Spor.WordsTxt
public import Certificates.Data.CFSGNative.Bridge.ONGPL
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import Std.Data.String.ToInt
import Std.Data.String.ToNat

public section

namespace CFSG.KS.Words

open CFSG.Sporadic.Bridge.ONGPL.Native CFSG.KC.Enum CFSG.KS.SporSch.LyTxt

private noncomputable def lwP (f t : List Char) : List Int := (List.splitOnPPrepend (· == ' ') f t).filterMap tv

private def TokInv (sg v : Nat) (tok : Bool) (t : List Char) : Prop :=
  (tok = false → v = 0 ∧ ((sg = 0 ∧ t = []) ∨ (sg = 1 ∧ t = ['-']))) ∧
  (tok = true → ∃ ds : List Char, ds ≠ [] ∧ (∀ c ∈ ds, c.isDigit = true) ∧
    v = Nat.ofDigitChars 10 ds 0 ∧ ((sg = 0 ∧ t = ds.reverse) ∨ (sg = 1 ∧ t = ds.reverse ++ ['-'])))

private theorem tv_minus : tv ['-'] = none := by
  unfold tv
  rw [Option.eq_none_iff_forall_ne_some]
  intro a ha
  rcases String.toInt?_eq_some_iff.1 ha with ⟨b, hb, -⟩ | ⟨t, ht, b, hb, -⟩
  · have h1 := (String.isNat_iff.1 (String.isNat_of_toNat?_eq_some hb)).2.1 '-' (by simp)
    revert h1
    decide
  · have e : t = "" := by
      apply String.toList_injective
      have := congrArg String.toList ht
      simpa using this
    subst e
    exact (String.isNat_iff.1 (String.isNat_of_toNat?_eq_some hb)).1 rfl

private theorem tv_none {sg v : Nat} {t : List Char} (h : TokInv sg v false t) : tv t.reverse = none := by
  rcases (h.1 rfl).2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact tv_nil
  · exact tv_minus

private theorem decW_push : ∀ (L acc c : Nat), c < 16 →
    decW (acc * 16 + c) (L + 1) = decW acc L ++ [letterOfCode c]
  | 0, acc, c, hc => by
    simp only [decW, Nat.mul_zero, Nat.shiftRight_zero, List.nil_append]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  | L + 1, acc, c, hc => by
    have e : (acc * 16 + c) >>> (4 * (L + 1)) = acc >>> (4 * L) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.mul_add, Nat.mul_one,
        Nat.add_comm (4 * L), Nat.pow_add, ← Nat.div_div_eq_div_mul]
      have e16 : (2 : Nat) ^ 4 = 16 := rfl
      rw [e16]
      congr 1
      omega
    rw [decW, decW_push L acc c hc, decW, List.cons_append, e]

private theorem push_ok {sg v acc len : Nat} {t : List Char} (ht : TokInv sg v true t)
    (h : (push true sg v acc).1 = true) :
    ∃ x, tv t.reverse = some x ∧ decW (push true sg v acc).2 (len + 1) = decW acc len ++ [x] := by
  obtain ⟨ds, hne, hd, hv, hs⟩ := ht.2 rfl
  unfold push at h ⊢
  simp only [bAnd_eqT, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨h0, h8⟩ := h
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨(v : Int), by rw [List.reverse_reverse, tv_pos hd hne, hv], ?_⟩
    change decW (acc * 16 + (2 * (v - 1) + 0)) (len + 1) = _
    have e : letterOfCode (2 * (v - 1) + 0) = (v : Int) := by
      unfold letterOfCode
      rw [ite_eq_left (by omega)]
      omega
    rw [decW_push len acc _ (by omega), e]
  · refine ⟨-(v : Int), by rw [List.reverse_append, List.reverse_reverse, List.reverse_singleton,
      List.singleton_append, tv_neg hd hne, hv], ?_⟩
    change decW (acc * 16 + (2 * (v - 1) + 1)) (len + 1) = _
    have e : letterOfCode (2 * (v - 1) + 1) = -(v : Int) := by
      unfold letterOfCode
      rw [ite_eq_right (by omega)]
      omega
    rw [decW_push len acc _ (by omega), e]

private theorem lwP_nil (t : List Char) : lwP [] t = (tv t.reverse).toList := by
  unfold lwP
  rw [List.splitOnPPrepend_nil, List.filterMap_cons, List.filterMap_nil]
  cases tv t.reverse <;> rfl

private theorem fin_ok {WC WL : Nat → Nat} {k acc len sg v : Nat} {tok : Bool} {t la : List Char} {pre : List Int} {X : Bool}
    (hw : decW acc len = pre) (ht : TokInv sg v tok t) (hl : ∀ f, lwP (la.reverse ++ f) [] = pre ++ lwP f t)
    (h : bIf(tok,
          strictB (push true sg v acc).2 fun a => bAnd((push true sg v acc).1,
            bAnd(Nat.beq a (WC k), bAnd(Nat.beq (Nat.succ len) (WL k), X))),
          bAnd(Nat.beq acc (WC k), bAnd(Nat.beq len (WL k), X))) = true) :
    lwP la.reverse [] = decW (WC k) (WL k) ∧ X = true := by
  have hl0 := hl []
  rw [List.append_nil, lwP_nil] at hl0
  cases tok
  · simp only [bAnd_eqT, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [tv_none ht, Option.toList_none, List.append_nil] at hl0
    refine ⟨?_, h3⟩
    rw [hl0, ← hw, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  · simp only [strictB_eqT, bAnd_eqT, Bool.and_eq_true] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    obtain ⟨x, hx, hd⟩ := push_ok (len := len) ht h0
    rw [hx, Option.toList_some] at hl0
    refine ⟨?_, h3⟩
    rw [hl0, ← hw, ← hd, Nat.eq_of_beq_eq_true h1, ← Nat.eq_of_beq_eq_true h2]

private theorem run_cons (WC WL : Nat → Nat) (N : Nat) (ch : Char) (cs : List Char)
    (k acc len sg v : Nat) (tok ne : Bool) :
    run WC WL N (ch :: cs) k acc len sg v tok ne = strictB (Char.toNat ch) fun c =>
      bIf(Nat.beq c (nat_lit 10),
        bIf(ne,
          bIf(tok,
            strictB (push true sg v acc).2 fun a => bAnd((push true sg v acc).1,
              bAnd(Nat.beq a (WC k), bAnd(Nat.beq (Nat.succ len) (WL k),
                run WC WL N cs (Nat.succ k) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) false false))),
            bAnd(Nat.beq acc (WC k), bAnd(Nat.beq len (WL k),
              run WC WL N cs (Nat.succ k) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) false false))),
          run WC WL N cs k acc len sg v tok ne),
      bIf(Nat.beq c (nat_lit 32),
        bIf(tok,
          strictB (push true sg v acc).2 fun a => bAnd((push true sg v acc).1,
            run WC WL N cs k a (Nat.succ len) (nat_lit 0) (nat_lit 0) false true),
          run WC WL N cs k acc len (nat_lit 0) (nat_lit 0) false true),
      bIf(Nat.beq c (nat_lit 45),
        bIf(tok, false, bIf(Nat.beq sg (nat_lit 0), run WC WL N cs k acc len (nat_lit 1) v false true,
          false)),
      bIf(Nat.ble (nat_lit 48) c, bIf(Nat.blt c (nat_lit 58),
          strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) fun v' =>
            run WC WL N cs k acc len sg v' true true,
          false), false)))) := rfl

private theorem not_nl {ch : Char} (h : Nat.beq ch.toNat 10 = false) : (ch == '\n') = false := by
  have := ne_of_beq_false h (by decide)
  simpa using this

private theorem not_sp {ch : Char} (h : Nat.beq ch.toNat 32 = false) : (ch == ' ') = false := by
  have := ne_of_beq_false h (by decide)
  simpa using this

private theorem fresh_inv : TokInv 0 0 false [] :=
  ⟨fun _ => ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, fun h => absurd h Bool.false_ne_true⟩

private theorem run_inv (WC WL : Nat → Nat) (N : Nat) : ∀ (cs : List Char) (k acc len sg v : Nat)
    (tok ne : Bool) (pre : List Int) (t la : List Char),
    decW acc len = pre → TokInv sg v tok t → (ne = false ↔ la = []) →
    (∀ f, lwP (la.reverse ++ f) [] = pre ++ lwP f t) →
    run WC WL N cs k acc len sg v tok ne = true →
    k ≤ N ∧ ((List.splitOnPPrepend (· == '\n') cs la).filter (fun l => !l.isEmpty)).map
      (fun p => lwP p []) = (List.range' k (N - k)).map fun j => decW (WC j) (WL j)
  | [], k, acc, len, sg, v, tok, ne, pre, t, la, hw, ht, hne, hl, h => by
    rw [List.splitOnPPrepend_nil]
    cases ne
    · have hla : la = [] := hne.1 rfl
      subst hla
      have hk : k = N := Nat.eq_of_beq_eq_true h
      subst hk
      simp
    · have hla : la ≠ [] := fun e => absurd (hne.2 e) (by decide)
      obtain ⟨h1, h2⟩ := fin_ok hw ht hl h
      have hk : k + 1 = N := Nat.eq_of_beq_eq_true h2
      subst hk
      have hla' : (!la.reverse.isEmpty) = true := by simpa using hla
      rw [List.filter_cons_of_pos (p := fun l : List Char => !l.isEmpty) hla']
      simp [h1]
  | ch :: cs, k, acc, len, sg, v, tok, ne, pre, t, la, hw, ht, hne, hl, h => by
    rw [run_cons, strictB_eqT] at h
    by_cases h10 : Nat.beq ch.toNat 10 = true
    · have hc : ch = '\n' := char_of_beq h10 (by decide)
      subst hc
      simp only [h10] at h
      rw [List.splitOnPPrepend_cons_pos (by decide), ← List.splitOnPPrepend_nil_right]
      cases ne
      · have hla : la = [] := hne.1 rfl
        subst hla
        simp only [] at h
        have := run_inv WC WL N cs k acc len sg v tok false pre t [] hw ht hne hl h
        simpa using this
      · have hla : la ≠ [] := fun e => absurd (hne.2 e) (by decide)
        simp only [] at h
        obtain ⟨h1, h2⟩ := fin_ok hw ht hl h
        obtain ⟨hk, ih⟩ := run_inv WC WL N cs (k + 1) 0 0 0 0 false false [] [] [] rfl fresh_inv
          (by simp) (fun f => by simp [lwP]) h2
        have hla' : (!la.reverse.isEmpty) = true := by simpa using hla
        refine ⟨by omega, ?_⟩
        rw [List.filter_cons_of_pos (p := fun l : List Char => !l.isEmpty) hla', List.map_cons, ih, h1,
          show N - k = (N - (k + 1)) + 1 by omega, List.range'_succ, List.map_cons]
    · have h10' : Nat.beq ch.toNat 10 = false := Bool.eq_false_iff.2 h10
      simp only [h10'] at h
      rw [List.splitOnPPrepend_cons_neg (p := fun x => x == '\n') (not_nl h10')]
      have hne' : (true = false ↔ ch :: la = []) := by simp
      by_cases h32 : Nat.beq ch.toNat 32 = true
      · have hc : ch = ' ' := char_of_beq h32 (by decide)
        subst hc
        simp only [h32] at h
        cases tok
        · simp only [] at h
          refine run_inv WC WL N cs k acc len 0 0 false true pre [] (' ' :: la) hw fresh_inv hne'
            (fun f => ?_) h
          rw [List.reverse_cons, List.append_assoc, List.singleton_append, hl]
          unfold lwP
          rw [List.splitOnPPrepend_cons_pos (by decide), List.filterMap_cons, tv_none ht,
            List.splitOnPPrepend_nil_right]
        · simp only [strictB_eqT, bAnd_eqT, Bool.and_eq_true] at h
          obtain ⟨h0, h⟩ := h
          obtain ⟨x, hx, hd⟩ := push_ok (len := len) ht h0
          refine run_inv WC WL N cs k _ (len + 1) 0 0 false true (pre ++ [x]) [] (' ' :: la)
            (by rw [hd, hw]) fresh_inv hne' (fun f => ?_) h
          rw [List.reverse_cons, List.append_assoc, List.singleton_append, hl]
          unfold lwP
          rw [List.splitOnPPrepend_cons_pos (by decide), List.filterMap_cons, hx]
          simp
      · have h32' : Nat.beq ch.toNat 32 = false := Bool.eq_false_iff.2 h32
        simp only [h32'] at h
        have hstep : ∀ t', (∀ f, lwP (ch :: f) t = lwP f t') →
            ∀ f, lwP ((ch :: la).reverse ++ f) [] = pre ++ lwP f t' := fun t' e f => by
          rw [List.reverse_cons, List.append_assoc, List.singleton_append, hl, e]
        have hsp : ∀ f t'', lwP (ch :: f) t'' = lwP f (ch :: t'') := fun f t'' => by
          unfold lwP
          rw [List.splitOnPPrepend_cons_neg (p := fun x => x == ' ') (not_sp h32')]
        by_cases h45 : Nat.beq ch.toNat 45 = true
        · have hc : ch = '-' := char_of_beq h45 (by decide)
          subst hc
          simp only [h45] at h
          cases tok
          · simp only [] at h
            by_cases hs0 : Nat.beq sg 0 = true
            · simp only [hs0] at h
              have hsg : sg = 0 := Nat.eq_of_beq_eq_true hs0
              obtain ⟨hv, hts⟩ := ht.1 rfl
              have htn : t = [] := by
                rcases hts with ⟨-, e⟩ | ⟨e, -⟩
                · exact e
                · omega
              subst htn
              refine run_inv WC WL N cs k acc len 1 v false true pre ['-'] ('-' :: la) hw
                ⟨fun _ => ⟨hv, Or.inr ⟨rfl, rfl⟩⟩, fun h => absurd h Bool.false_ne_true⟩ hne'
                (hstep _ fun f => hsp f []) h
            · have hs0' : Nat.beq sg 0 = false := Bool.eq_false_iff.2 hs0
              simp only [hs0'] at h
              exact absurd h Bool.false_ne_true
          · exact absurd h Bool.false_ne_true
        · have h45' : Nat.beq ch.toNat 45 = false := Bool.eq_false_iff.2 h45
          simp only [h45'] at h
          by_cases hlo : Nat.ble 48 ch.toNat = true
          · simp only [hlo] at h
            by_cases hhi : Nat.blt ch.toNat 58 = true
            · simp only [hhi, strictB_eqT] at h
              have hdc : ch.isDigit = true := isDigit_of (by
                rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
                exact ⟨Nat.le_of_ble_eq_true hlo, by have := Nat.le_of_ble_eq_true hhi; omega⟩)
              have ht' : TokInv sg (v * 10 + (ch.toNat - 48)) true (ch :: t) := by
                refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
                cases tok
                · obtain ⟨hv, hts⟩ := ht.1 rfl
                  refine ⟨[ch], by simp, by simpa using hdc, ?_, ?_⟩
                  · have e := ofDigitChars_snoc [] ch
                    rw [List.nil_append, Nat.ofDigitChars_nil] at e
                    rw [hv, e]
                  · rcases hts with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
                    · exact Or.inl ⟨hs, rfl⟩
                    · exact Or.inr ⟨hs, rfl⟩
                · obtain ⟨ds, hne1, hd, hv, hts⟩ := ht.2 rfl
                  refine ⟨ds ++ [ch], by simp, fun c hc => ?_, by rw [ofDigitChars_snoc, hv], ?_⟩
                  · rcases List.mem_append.1 hc with hc | hc
                    · exact hd c hc
                    · rw [List.mem_singleton.1 hc]
                      exact hdc
                  · rcases hts with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
                    · exact Or.inl ⟨hs, by simp⟩
                    · exact Or.inr ⟨hs, by simp⟩
              exact run_inv WC WL N cs k acc len sg _ true true pre (ch :: t) (ch :: la) hw ht' hne'
                (hstep _ fun f => hsp f t) h
            · have hhi' : Nat.blt ch.toNat 58 = false := Bool.eq_false_iff.2 hhi
              simp only [hhi'] at h
              exact absurd h Bool.false_ne_true
          · have hlo' : Nat.ble 48 ch.toNat = false := Bool.eq_false_iff.2 hlo
            simp only [hlo'] at h
            exact absurd h Bool.false_ne_true

theorem wordsK_sound {cs : List Char} {WC WL : Nat → Nat} {N : Nat} (h : wordsK cs WC WL N = true) :
    parseWords (String.ofList cs) = Array.ofFn (n := N) fun k => decW (WC k.val) (WL k.val) := by
  obtain ⟨-, e⟩ := run_inv WC WL N cs 0 0 0 0 0 false false [] [] [] rfl fresh_inv (by simp)
    (fun f => by simp [lwP]) h
  have hpl : ∀ p : List Char, parseLine (String.ofList p) = lwP p [] := fun p => by
    unfold parseLine lwP
    rw [splitOn_sp, List.filterMap_map, List.splitOnPPrepend_nil_right]
    rfl
  have hfl : ((String.ofList cs).splitOn "\n").filter (fun l => !l.isEmpty) =
      ((List.splitOnPPrepend (· == '\n') cs []).filter (fun l => !l.isEmpty)).map String.ofList := by
    rw [splitOn_nl, List.filter_map, List.splitOnPPrepend_nil_right]
    congr 2
    funext p
    have hiso : (String.ofList p).isEmpty = p.isEmpty := by
      rw [Bool.eq_iff_iff, String.isEmpty_iff, List.isEmpty_iff, String.ofList_eq_empty_iff]
    change (!(String.ofList p).isEmpty) = !p.isEmpty
    rw [hiso]
  unfold parseWords
  rw [hfl, List.map_map]
  have hf : parseLine ∘ String.ofList = fun p => lwP p [] := funext hpl
  rw [hf, e, Nat.sub_zero]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

end CFSG.KS.Words

end
