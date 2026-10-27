module

public import Certificates.Data.Kernel.MtxK
public import CFSG.Sporadic.SuzOddCore.Arrays
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Batteries.Data.String.Lemmas
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.Mtx

open CFSG.KS.Raw CFSG.KC.Enum CFSG.KS

private theorem forIn_yield {L : List Char}
    {f : Char → Option Bool × Bool → Id (ForInStep (Option Bool × Bool))}
    (hf : ∀ c ∈ L, ∀ s, f c s = pure (.yield (none, true))) :
    ∀ s, forIn L s f = pure (if L = [] then s else (none, true)) := by
  induction L with
  | nil => intro s; rfl
  | cons c L ih =>
    intro s
    rw [List.forIn_cons, hf c List.mem_cons_self s]
    change forIn L (none, true) f = _
    rw [ih (fun c hc s => hf c (List.mem_cons_of_mem _ hc) s)]
    simp

private theorem digit_ne {c : Char} (h : c.isDigit = true) : c ≠ '_' := by
  rintro rfl
  exact absurd h (by decide)

private theorem isNat_digits (ds : List Char) (hd : ∀ c ∈ ds, c.isDigit = true) :
    (String.ofList ds).toSlice.isNat = !ds.isEmpty := by
  unfold String.Slice.isNat
  simp only [String.Slice.forIn_eq_forIn_toList, String.copy_toSlice, String.toList_ofList]
  rw [forIn_yield]
  · cases ds <;> rfl
  · intro c hc s
    simp [digit_ne (hd c hc), hd c hc]

private theorem foldl_digits : ∀ (L : List Char) (acc : Nat), (∀ c ∈ L, c.isDigit = true) →
    L.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) acc =
      L.foldl (fun n c => n * 10 + (c.toNat - 48)) acc
  | [], _, _ => rfl
  | c :: L, acc, h => by
    rw [List.foldl_cons, List.foldl_cons, ite_eq_right (digit_ne (h c List.mem_cons_self))]
    exact foldl_digits L _ fun c hc => h c (List.mem_cons_of_mem _ hc)

private noncomputable def nOf (ds : List Char) : Nat :=
  ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

private theorem tokD (ds : List Char) (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) :
    (String.ofList ds).toNat? = some (nOf ds) := by
  unfold String.toNat? String.Slice.toNat?
  rw [isNat_digits ds hd]
  cases ds with
  | nil => exact absurd rfl hne
  | cons c L =>
    simp only [List.isEmpty_cons, Bool.not_false, ↓reduceIte,
      String.Slice.foldl_eq_foldl_toList, String.copy_toSlice, String.toList_ofList]
    exact congrArg some (foldl_digits (c :: L) 0 hd)

private theorem toNat_eq {c d : Char} : c = d ↔ c.toNat = d.toNat := Char.toNat_inj.symm

private theorem nbeq (a b : Nat) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, decide_eq_true_iff])

private theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = (c && t || !c && e) := by
  cases c <;> cases t <;> cases e <;> rfl

private theorem wsB_eq (c : Char) : wsB c.toNat = c.isWhitespace := by
  unfold wsB Char.isWhitespace
  simp only [bIf_eq, nbeq, toNat_eq]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  by_cases a : c.toNat = 32 <;> by_cases b : c.toNat = 10 <;> by_cases d : c.toNat = 9 <;>
    by_cases f : c.toNat = 13 <;> simp [a, b, d, f]

private theorem isDigit_iff (c : Char) : c.isDigit = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  unfold Char.isDigit
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le]
  rfl

private theorem digV_eq (c : Char) :
    CFSG.KC.SurjK.digV c.toNat = if c.isDigit = true then c.toNat - 48 else 10 := by
  unfold CFSG.KC.SurjK.digV CFSG.KLie.CT.andB
  by_cases h : c.isDigit = true
  · have h' := (isDigit_iff c).1 h
    rw [Nat.ble_eq_true_of_le h'.1, Nat.ble_eq_true_of_le h'.2, PackFld.iteT h]
    rfl
  · rw [PackFld.iteF h]
    cases e1 : Nat.ble 48 c.toNat
    · rfl
    · cases e2 : Nat.ble c.toNat 57
      · rfl
      · exact absurd ((isDigit_iff c).2 ⟨Nat.le_of_ble_eq_true e1, Nat.le_of_ble_eq_true e2⟩) h

private theorem ws_not_digit {c : Char} (h : c.isDigit = true) : c.isWhitespace = false := by
  have h' := (isDigit_iff c).1 h
  rw [← wsB_eq]
  unfold wsB
  simp only [bIf_eq, nbeq]
  have : ¬ c.toNat = 32 := by omega
  have : ¬ c.toNat = 10 := by omega
  have : ¬ c.toNat = 9 := by omega
  have : ¬ c.toNat = 13 := by omega
  simp [*]

@[expose] noncomputable def runT (n : Nat) (tok : Nat → Nat → Bool) (cs : List Char) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun k v dg => bIf(Nat.beq dg 1, bAnd(tok k v, Nat.beq (Nat.succ k) (Nat.add n 4)),
      Nat.beq k (Nat.add n 4)))
    (fun ch _ ih k v dg => strictB (Char.toNat ch) fun c =>
      bIf(Nat.blt (CFSG.KC.SurjK.digV c) 10,
        ih k (Nat.add (Nat.mul v 10) (CFSG.KC.SurjK.digV c)) 1,
      bIf(wsB c, bIf(Nat.beq dg 1, bAnd(tok k v, ih (Nat.succ k) 0 0), ih k 0 0), false)))
    cs

theorem mtxRun_eq (n w P : Nat) (cs : List Char) : mtxRun n w P cs = runT n (tokOK w P) cs :=
  rfl

private def toksOf (l : List (List Char)) : List (List Char) := l.filter fun p => !p.isEmpty

private theorem mtx_run (n : Nat) (tok : Nat → Nat → Bool) :
    ∀ (cs : List Char) (k : Nat) (cur : List Char),
    (∀ c ∈ cur, c.isDigit = true) →
    runT n tok cs k (nOf cur) (if cur = [] then 0 else 1) = true →
    (∀ p ∈ toksOf (List.splitOnPPrepend Char.isWhitespace cs cur.reverse), ∀ c ∈ p,
      c.isDigit = true) ∧
      k + (toksOf (List.splitOnPPrepend Char.isWhitespace cs cur.reverse)).length = n + 4 ∧
      ∀ i (hi : i < (toksOf (List.splitOnPPrepend Char.isWhitespace cs cur.reverse)).length),
        tok (k + i) (nOf (toksOf (List.splitOnPPrepend Char.isWhitespace cs cur.reverse))[i])
          = true
  | [], k, cur, hd, h => by
    rw [List.splitOnPPrepend_nil, List.reverse_reverse]
    change bIf(Nat.beq (if cur = [] then 0 else 1) 1,
      bAnd(tok k (nOf cur), Nat.beq (Nat.succ k) (Nat.add n 4)),
      Nat.beq k (Nat.add n 4)) = true at h
    by_cases hc : cur = []
    · subst hc
      have e : Nat.beq k (Nat.add n 4) = true := h
      have e' := Nat.eq_of_beq_eq_true e
      refine ⟨by simp [toksOf], by simp [toksOf]; exact e',
        fun i hi => absurd hi (by simp [toksOf])⟩
    · rw [PackFld.iteF hc] at h
      change bAnd(tok k (nOf cur), Nat.beq (Nat.succ k) (Nat.add n 4)) = true at h
      rw [bAnd_iff] at h
      have ht : toksOf [cur] = [cur] := by
        cases cur with
        | nil => exact absurd rfl hc
        | cons _ _ => rfl
      rw [ht]
      refine ⟨fun p hp => by rw [List.mem_singleton.mp hp]; exact hd, ?_, fun i hi => ?_⟩
      · have := Nat.eq_of_beq_eq_true h.2
        simp only [List.length_singleton]
        exact this
      · have : i = 0 := by simpa using hi
        subst this
        exact h.1
  | ch :: cs, k, cur, hd, h => by
    change strictB (Char.toNat ch) (fun c =>
      bIf(Nat.blt (CFSG.KC.SurjK.digV c) 10,
        runT n tok cs k (Nat.add (Nat.mul (nOf cur) 10) (CFSG.KC.SurjK.digV c)) 1,
      bIf(wsB c, bIf(Nat.beq (if cur = [] then 0 else 1) 1,
        bAnd(tok k (nOf cur), runT n tok cs (Nat.succ k) 0 0),
        runT n tok cs k 0 0), false))) = true at h
    rw [PackFld.strictB_eqP, digV_eq, wsB_eq] at h
    rw [List.splitOnPPrepend_cons_eq_ite]
    by_cases hdg : ch.isDigit = true
    · rw [PackFld.iteT hdg] at h
      have hlt : Nat.blt (ch.toNat - 48) 10 = true := by
        have := (isDigit_iff ch).1 hdg
        exact Nat.blt_eq.mpr (by omega)
      rw [hlt] at h
      change runT n tok cs k (Nat.add (Nat.mul (nOf cur) 10) (ch.toNat - 48)) 1 = true at h
      have hd' : ∀ c ∈ cur ++ [ch], c.isDigit = true := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hd c hc
        · rw [List.mem_singleton.mp hc]
          exact hdg
      have e1 : Nat.add (Nat.mul (nOf cur) 10) (ch.toNat - 48) = nOf (cur ++ [ch]) := by
        unfold nOf
        rw [List.foldl_append]
        rfl
      have e2 : (if cur ++ [ch] = [] then 0 else 1) = 1 := by simp
      rw [e1, ← e2] at h
      have := mtx_run n tok cs k (cur ++ [ch]) hd' h
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at this
      rw [ws_not_digit hdg]
      exact this
    · rw [PackFld.iteF hdg] at h
      have hlt : Nat.blt 10 10 = false := rfl
      rw [hlt] at h
      change bIf(ch.isWhitespace, bIf(Nat.beq (if cur = [] then 0 else 1) 1,
        bAnd(tok k (nOf cur), runT n tok cs (Nat.succ k) 0 0),
        runT n tok cs k 0 0), false) = true at h
      cases hw : ch.isWhitespace <;> rw [hw] at h
      · exact absurd h Bool.false_ne_true
      change bIf(Nat.beq (if cur = [] then 0 else 1) 1,
        bAnd(tok k (nOf cur), runT n tok cs (Nat.succ k) 0 0),
        runT n tok cs k 0 0) = true at h
      simp only [↓reduceIte, List.reverse_reverse]
      rw [List.splitOnP_eq_splitOnPPrepend]
      have e0 : (0 : Nat) = nOf [] := rfl
      have ef : (0 : Nat) = if ([] : List Char) = [] then 0 else 1 := rfl
      by_cases hc : cur = []
      · subst hc
        change runT n tok cs k 0 0 = true at h
        rw [e0] at h
        conv at h => rhs; skip
        have h' : runT n tok cs k (nOf []) (if ([] : List Char) = [] then 0 else 1) = true := h
        have := mtx_run n tok cs k [] (fun c hc => absurd hc List.not_mem_nil) h'
        simpa [toksOf] using this
      · rw [PackFld.iteF hc] at h
        change bAnd(tok k (nOf cur), runT n tok cs (Nat.succ k) 0 0) = true at h
        rw [bAnd_iff] at h
        have h' : runT n tok cs (k + 1) (nOf []) (if ([] : List Char) = [] then 0 else 1) =
          true := h.2
        obtain ⟨a, b, c⟩ := mtx_run n tok cs (k + 1) [] (fun c hc => absurd hc List.not_mem_nil) h'
        simp only [List.reverse_nil] at a b c
        have ht : toksOf (cur :: List.splitOnPPrepend Char.isWhitespace cs []) =
            cur :: toksOf (List.splitOnPPrepend Char.isWhitespace cs []) := by
          cases cur with
          | nil => exact absurd rfl hc
          | cons _ _ => rfl
        simp only [ht]
        refine ⟨fun p hp => ?_, by simp only [List.length_cons]; omega, fun i hi => ?_⟩
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact hd
          · exact a p hp
        · rcases i with _ | i
          · exact h.1
          · rw [List.getElem_cons_succ, show k + (i + 1) = k + 1 + i by omega]
            exact c i (by simpa using hi)

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem runT_sound {n : Nat} {tok : Nat → Nat → Bool} {cs : List Char}
    (h : runT n tok cs 0 0 0 = true) :
    (CFSG.Sporadic.SuzOddCore.mtxTokens (String.ofList cs)).length = n + 4 ∧
      ∀ i < n + 4, tok i (CFSG.Sporadic.SuzOddCore.tokenVal
        ((CFSG.Sporadic.SuzOddCore.mtxTokens (String.ofList cs)).getD i "")) = true := by
  obtain ⟨hd, hl, ht⟩ := mtx_run n tok cs 0 [] (fun c hc => absurd hc List.not_mem_nil) h
  generalize hT0 : toksOf (List.splitOnPPrepend Char.isWhitespace cs ([] : List Char).reverse) = T
    at hd hl ht
  have hT : toksOf (List.splitOnP Char.isWhitespace cs) = T := by
    rw [List.splitOnP_eq_splitOnPPrepend]
    exact hT0
  simp only [Nat.zero_add] at hl ht
  have htok : CFSG.Sporadic.SuzOddCore.mtxTokens (String.ofList cs) = T.map String.ofList := by
    unfold CFSG.Sporadic.SuzOddCore.mtxTokens
    rw [String.splitToList_of_valid, String.toList_ofList, ← hT, toksOf, List.filter_map]
    congr 1
    apply List.filter_congr
    intro p _
    cases p <;> simp
  have hval : ∀ p ∈ T, CFSG.Sporadic.SuzOddCore.tokenVal (String.ofList p) = nOf p := by
    intro p hp
    unfold CFSG.Sporadic.SuzOddCore.tokenVal
    have hne : p ≠ [] := by
      rw [← hT] at hp
      unfold toksOf at hp
      intro e
      subst e
      simp at hp
    rw [tokD p (hd p hp) hne]
    rfl
  rw [htok, List.length_map]
  refine ⟨hl, fun i hi => ?_⟩
  have hi' : i < T.length := by omega
  rw [getD_of_lt _ (by simpa using hi'), List.getElem_map, hval _ (List.getElem_mem _)]
  exact ht i hi'

theorem field_of_tok {w P k v : Nat}
    (h : bAnd(Nat.ble 1 v, Nat.beq (pg w (mask w) P (Nat.sub k 4)) (Nat.sub v 1)) = true) :
    v - 1 = pg w (mask w) P (k - 4) := by
  rw [bAnd_iff] at h
  exact (Nat.eq_of_beq_eq_true h.2).symm

theorem mtxArr_of_tokens {n w P : Nat} {s : String}
    (hl : (CFSG.Sporadic.SuzOddCore.mtxTokens s).length = n + 4)
    (ht : ∀ i < n, CFSG.Sporadic.SuzOddCore.tokenVal
      ((CFSG.Sporadic.SuzOddCore.mtxTokens s).getD (4 + i) "") - 1 = pg w (mask w) P i) :
    CFSG.Sporadic.SuzOddCore.mtxArr s = unpack n w P := by
  unfold CFSG.Sporadic.SuzOddCore.mtxArr CFSG.Sporadic.SuzOddCore.mtxImages
  apply Array.ext
  · simp [unpack]
    omega
  · intro i h1 h2
    have hi : i < n := by simpa [unpack] using h2
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_drop, unpack,
      Array.getElem_ofFn]
    have := ht i hi
    rwa [getD_of_lt _ (by omega)] at this

theorem mtxK_sound {n w P : Nat} {cs : List Char} (h : mtxK n w P cs = true) :
    CFSG.Sporadic.SuzOddCore.mtxArr (String.ofList cs) = unpack n w P := by
  obtain ⟨hl, ht⟩ := runT_sound (tok := tokOK w P) h
  refine mtxArr_of_tokens hl fun i hi => ?_
  have := ht (4 + i) (by omega)
  unfold tokOK at this
  have h4 : Nat.blt (4 + i) 4 = false := by
    cases e : Nat.blt (4 + i) 4
    · rfl
    · have := Nat.blt_eq.mp e
      omega
  rw [h4] at this
  have e := field_of_tok this
  rwa [Nat.add_sub_cancel_left] at e

end CFSG.KC.Mtx

end
