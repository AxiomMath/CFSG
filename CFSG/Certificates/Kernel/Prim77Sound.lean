module

public import Certificates.Data.Kernel.Prim77.Checks
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Common.StrReplace
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77Data

public section

namespace CFSG.KS.Prim77

open CFSG.KC.Enum CFSG.KC.Over77 CFSG.KC.Prim77 CFSG.KS.PF CFSG.KS.Prim
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77
  (idA comp evalW parseWords parseNats dataS)
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = (if c = true then t else e) := by
  cases c <;> rfl

theorem im_eq (p i : Nat) : im p i = pg 7 (mask 7) p i := rfl

theorem idP_eq : idP = pidn 77 7 := rfl

theorem getD_of_lt {d : Array Nat} {i : Nat} (h : i < d.size) : d.getD i 0 = d[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

theorem getD_toArray {α : Type} (L : List α) (i : Nat) (x : α) :
    L.toArray.getD i x = L.getD i x := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem nth_eq : ∀ (L : List Nat) (i : Nat), nth L i = L.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => nth_eq L i

@[expose] def AR (a : Nat) (d : Array Nat) : Prop :=
  d.size = 77 ∧ ∀ i < 77, pg 7 (mask 7) a i < 77 ∧ d.getD i 0 = pg 7 (mask 7) a i

theorem ar_idP : AR idP idA := by
  refine ⟨by simp [idA], fun i hi => ?_⟩
  have h : pg 7 (mask 7) (pidn 77 7) i = i := pg_pidn (by decide) (by decide) hi
  rw [idP_eq, h]
  refine ⟨hi, ?_⟩
  rw [getD_of_lt (by simpa [idA] using hi)]
  simp [idA]

theorem getD_map (e : Array Nat) (f : Nat → Nat) {i : Nat} (hi : i < e.size) :
    (e.map f).getD i 0 = f (e.getD i 0) := by
  rw [getD_of_lt (by simpa using hi), getD_of_lt hi, Array.getElem_map]

theorem ar_cp {a b : Nat} {d e : Array Nat} (ha : AR a d) (hb : AR b e) :
    AR (cp a b) (comp d e) := by
  refine ⟨by simp [comp, hb.1], fun i hi => ?_⟩
  have hc : pg 7 (mask 7) (cp a b) i = pg 7 (mask 7) a (pg 7 (mask 7) b i) :=
    pg_pcomp (n := 77) (by decide) hi
  obtain ⟨hb1, hb2⟩ := hb.2 i hi
  obtain ⟨ha1, ha2⟩ := ha.2 _ hb1
  rw [hc]
  refine ⟨ha1, ?_⟩
  unfold comp
  rw [getD_map e _ (by rw [hb.1]; exact hi), hb2, ha2]

theorem ar_wordK {g : Nat → Nat} {e : Array (Array Nat)} (hg : ∀ k, AR (g k) (e.getD k idA)) :
    ∀ (w : List Nat) (acc : Nat) (A : Array Nat), AR acc A →
      AR (wordK g w acc) (w.foldl (fun acc k => comp acc (e.getD k idA)) A)
  | [], _, _, h => h
  | k :: w, acc, A, h => by
    have e1 : wordK g (k :: w) acc = wordK g w (cp acc (g k)) := by
      change strictN (cp acc (g k)) (fun x => wordK g w x) = _
      rw [strictN_eq']
    rw [e1, List.foldl_cons]
    exact ar_wordK hg w _ _ (ar_cp h (hg k))

theorem ar_evalW {g : Nat → Nat} {e : Array (Array Nat)} (hg : ∀ k, AR (g k) (e.getD k idA))
    (w : List Nat) : AR (wordK g w idP) (evalW e w) :=
  ar_wordK hg w idP idA ar_idP

theorem ar_powK {a : Nat} {d : Array Nat} (h : AR a d) : ∀ k, AR (powK a k) (powA d k)
  | 0 => ar_idP
  | k + 1 => by
    have e1 : powK a (k + 1) = cp (powK a k) a := by
      change strictN (powK a k) (fun v => cp v a) = _
      rw [strictN_eq']
    rw [e1]
    exact ar_cp (ar_powK h k) h

theorem ar_eq {a : Nat} {d d' : Array Nat} (h : AR a d) (h' : AR a d') : d = d' := by
  apply Array.ext (h.1.trans h'.1.symm)
  intro i hi hi'
  have hi77 : i < 77 := h.1 ▸ hi
  rw [← getD_of_lt hi, ← getD_of_lt hi', (h.2 i hi77).2, (h'.2 i hi77).2]

theorem ar_of_arK {a : Nat} {d : Array Nat} (h : arK a d = true) : AR a d := by
  unfold arK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hc : canonK 77 7 127 539 a = true := h2
  obtain ⟨-, -, -, hlt⟩ := canon_facts hc
  refine ⟨Nat.eq_of_beq_eq_true h1, fun i hi => ⟨hlt i hi, ?_⟩⟩
  exact (Nat.eq_of_beq_eq_true (allN_spec h3 i hi)).symm

theorem lettersData_getD (k : Nat) : lettersData.getD k idA =
    [dataS[0]!, powA dataS[0]! 2, dataS[2]!, powA dataS[2]! 4].getD k idA := by
  unfold lettersData
  exact getD_toArray _ _ _

theorem beq_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem let5_big (L0 L1 L2 L3 j : Nat) (hj : 4 ≤ j) : let5 L0 L1 L2 L3 j = idP := by
  have h0 : Nat.beq j (nat_lit 0) = false := beq_ne fun e => absurd (e ▸ hj) (by decide)
  have h1 : Nat.beq j (nat_lit 1) = false := beq_ne fun e => absurd (e ▸ hj) (by decide)
  have h2 : Nat.beq j (nat_lit 2) = false := beq_ne fun e => absurd (e ▸ hj) (by decide)
  have h3 : Nat.beq j (nat_lit 3) = false := beq_ne fun e => absurd (e ▸ hj) (by decide)
  unfold let5
  rw [h0, h1, h2, h3]

theorem ar_let5 {A C : Nat} (hA : AR A dataS[0]!) (hC : AR C dataS[2]!) (k : Nat) :
    AR (let5 A (powK A 2) C (powK C 4) k) (lettersData.getD k idA) := by
  rw [lettersData_getD]
  rcases k with _ | _ | _ | _ | k
  · rw [List.getD_cons_zero]
    exact hA
  · rw [List.getD_cons_succ, List.getD_cons_zero]
    exact ar_powK hA 2
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
    exact hC
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
    exact ar_powK hC 4
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_nil, let5_big _ _ _ _ _ (by omega)]
    exact ar_idP

theorem letsB_eq (A C : Nat) (f : Nat → Nat → Nat → Nat → Bool) :
    letsB A C f = f A (powK A 2) C (powK C 4) := by
  unfold letsB
  rw [strictB_eq', strictB_eq', strictB_eq', strictB_eq']

theorem nl_eq : ("\n" : String) = String.singleton '\n' := by decide

theorem sp_eq : (" " : String) = String.singleton ' ' := by decide

theorem colon_eq : (":" : String) = String.singleton ':' := by decide

theorem ofList_ne_empty (l : List Char) : decide (String.ofList l ≠ "") = !l.isEmpty := by
  cases l with
  | nil => simp
  | cons x xs =>
    have : String.ofList (x :: xs) ≠ "" := by
      intro h
      have := congrArg String.toList h
      simp at this
    simp [this]

theorem startsWith_colon (l : List Char) :
    (String.ofList l).startsWith ":" = [':'].isPrefixOf l := by
  apply Bool.eq_iff_iff.mpr
  rw [String.startsWith_string_iff, List.isPrefixOf_iff_prefix]
  simp

theorem toNat!_num {p : List Char} (h : isNum p = true) :
    (String.ofList p).toNat! = CFSG.KC.Str.decVal p := by
  unfold isNum at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at h
  exact CFSG.KC.Str.toNat!_ofList h.1 h.2

theorem numsK_spec : ∀ (ps : List (List Char)) (L : List Nat), numsK ps = some L →
    ps.map (fun t => (String.ofList t).toNat!) = L
  | [], L, h => by
    simp only [numsK, Option.some.injEq] at h
    simp [← h]
  | p :: ps, L, h => by
    unfold numsK at h
    split at h
    · rename_i hp
      cases e : numsK ps with
      | none => rw [e] at h; simp at h
      | some L' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [← h, List.map_cons, toNat!_num hp, numsK_spec ps L' e]
    · simp at h

theorem numsL_spec : ∀ (ps : List (List (List Char))) (L : List (List Nat)), numsL ps = some L →
    ps.map (fun l => l.map fun t => (String.ofList t).toNat!) = L
  | [], L, h => by
    simp only [numsL, Option.some.injEq] at h
    simp [← h]
  | p :: ps, L, h => by
    unfold numsL at h
    cases e : numsK p with
    | none => rw [e] at h; simp at h
    | some a =>
      cases e' : numsL ps with
      | none => rw [e, e'] at h; simp at h
      | some b =>
        rw [e, e'] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h, List.map_cons, numsK_spec p a e, numsL_spec ps b e']

theorem parseWords_eq (cs : List Char) : parseWords (String.ofList cs) =
    ((piecesW cs).map fun l => l.map fun t => (String.ofList t).toNat!).toArray := by
  unfold parseWords piecesW
  rw [nl_eq, CFSG.KC.Str.splitOn_ofList, List.filter_map, List.map_map, List.map_map]
  have e1 : ((fun l : String => l.startsWith ":") ∘ String.ofList) =
      fun l => [':'].isPrefixOf l := funext startsWith_colon
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply]
  rw [colon_eq, CFSG.KC.StrReplace.replace_char_ofList, sp_eq, CFSG.KC.Str.splitOn_ofList,
    List.filter_map, List.map_map]
  have e2 : ((fun t : String => decide (t ≠ "")) ∘ String.ofList) = fun l => !l.isEmpty :=
    funext ofList_ne_empty
  rw [e2]
  rfl

theorem parseWords_of {cs : List Char} {W : List (List Nat)} (h : wordsO cs = some W) :
    parseWords (String.ofList cs) = W.toArray := by
  rw [parseWords_eq, numsL_spec _ W h]

theorem parseNats_of {cs : List Char} {R : List Nat} (h : natsO cs = some R) :
    parseNats (String.ofList cs) = R.toArray := by
  unfold parseNats
  have e0 : (String.ofList cs).replace "\n" " " = String.ofList (cs.map CFSG.KC.StrNlSp.nlSp) := by
    apply String.toList_injective
    rw [CFSG.KC.StrNlSp.replace_nl_sp, String.toList_ofList, String.toList_ofList]
  rw [e0, sp_eq, CFSG.KC.Str.splitOn_ofList, List.filter_map]
  have e2 : ((fun t : String => decide (t ≠ "")) ∘ String.ofList) = fun l => !l.isEmpty :=
    funext ofList_ne_empty
  rw [e2, List.map_toArray, List.map_map]
  congr 1
  exact numsK_spec _ R h

theorem optB_spec {α : Type} {o : Option α} {f : α → Bool} (h : optB o f = true) :
    ∃ a, o = some a ∧ f a = true := by
  cases o with
  | none => exact absurd h (by simp [optB])
  | some a => exact ⟨a, rfl, h⟩

theorem transW_spec {g : Nat → Nat} : ∀ (W : List (List Nat)) (i : Nat), transW g W i = true →
    i + W.length = 77 ∧ ∀ j < W.length, im (wordK g (W.getD j []) idP) 0 = i + j
  | [], i, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun j hj => absurd hj (by simp)⟩
  | w :: W, i, h => by
    have e : transW g (w :: W) i =
        (Nat.beq (im (wordK g w idP) 0) i && transW g W (i + 1)) := bAnd_eq _ _
    rw [e, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := transW_spec W (i + 1) h.2
    refine ⟨by simp only [List.length_cons]; omega, fun j hj => ?_⟩
    rcases j with _ | j
    · exact Nat.eq_of_beq_eq_true h.1
    · have := h2 j (by simpa using hj)
      rw [List.getD_cons_succ, this]
      omega

theorem chkTrans_of {g : Nat → Nat} (hg : ∀ k, AR (g k) (lettersData.getD k idA))
    {W : List (List Nat)} (hW : transWords = W.toArray) (h : transK g W = true) :
    chkTrans = true := by
  obtain ⟨hl, hi⟩ := transW_spec W 0 h
  unfold chkTrans
  rw [hW, Bool.and_eq_true, List.all_eq_true]
  refine ⟨by simp; omega, fun i hi77 => ?_⟩
  rw [List.mem_range] at hi77
  have har := ar_evalW hg (W.getD i [])
  rw [beq_iff_eq, getD_toArray W i [], (har.2 0 (by decide)).2, ← im_eq, hi i (by omega)]
  simp

theorem cnt0_eq (r : Nat) : ∀ T : List Nat, cnt0 T r = T.countP (· == r)
  | [] => rfl
  | x :: T => by
    have e : cnt0 (x :: T) r = (if (Nat.beq x r) = true then 1 else 0) + cnt0 T r := by
      change Nat.add (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq x r)) (cnt0 T r) = _
      rw [nIf_eq]
      rfl
    rw [e, cnt0_eq r T, List.countP_cons]
    by_cases hx : x = r
    · subst hx
      simp [Nat.beq_refl]
      omega
    · simp [beq_ne hx, hx]

theorem cntK_eq (R : List Nat) (r : Nat) : cntK R r = R.tail.countP (· == r) := by
  cases R with
  | nil => rfl
  | cons x T => exact cnt0_eq r T

theorem countP_range_getD (r : Nat) : ∀ T : List Nat,
    (List.range T.length).countP (fun y => T.getD y 0 == r) = T.countP (· == r)
  | [] => rfl
  | x :: T => by
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
      List.countP_cons]
    have e : ((fun y => (x :: T).getD y 0 == r) ∘ Nat.succ) = fun y => T.getD y 0 == r := by
      funext y
      simp
    rw [e, countP_range_getD r T]
    simp

theorem countP_rep {R : List Nat} (hR : R.length = 77) (r : Nat) :
    (List.range 77).countP (fun y => decide (y ≠ 0) && R.toArray.getD y 0 == r) =
      R.tail.countP (· == r) := by
  obtain ⟨x, T, rfl⟩ : ∃ x T, R = x :: T := by
    cases R with
    | nil => simp at hR
    | cons x T => exact ⟨x, T, rfl⟩
  have hT : T.length = 76 := by simpa using hR
  rw [show (77 : Nat) = T.length + 1 by omega, List.range_succ_eq_map, List.countP_cons,
    List.countP_map, List.tail_cons, ← countP_range_getD r T]
  have e : ((fun y => decide (y ≠ 0) && (x :: T).toArray.getD y 0 == r) ∘ Nat.succ) =
      fun y => T.getD y 0 == r := by
    funext y
    simp [getD_toArray]
  rw [e]
  simp

theorem stabAt_spec {g : Nat → Nat} {R : List Nat} {w : List Nat} {r i : Nat}
    (h : stabAt g R w r i = true) :
    im (wordK g w idP) 0 = 0 ∧ r < 77 ∧ im (wordK g w idP) r = i ∧
      12 ≤ R.tail.countP (· == r) := by
  unfold stabAt at h
  rw [strictB_eq', bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3, ?_⟩
  rw [← cntK_eq]
  exact Nat.le_of_ble_eq_true h4

theorem stabW_spec {g : Nat → Nat} {R : List Nat} : ∀ (W : List (List Nat)) (i : Nat),
    stabW g R W i = true → i + W.length = 77 ∧ ∀ j < W.length, i + j ≠ 0 →
      stabAt g R (W.getD j []) (R.getD (i + j) 0) (i + j) = true
  | [], i, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun j hj => absurd hj (by simp)⟩
  | w :: W, i, h => by
    have e : stabW g R (w :: W) i =
        ((if Nat.beq i 0 then true else stabAt g R w (nth R i) i) && stabW g R W (i + 1)) := by
      change Bool.rec (motive := fun _ => Bool) false (stabW g R W (Nat.succ i))
        (Bool.rec (motive := fun _ => Bool) (stabAt g R w (nth R i) i) true (Nat.beq i 0)) = _
      rw [bAnd_eq, bIf_eq]
    rw [e, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := stabW_spec W (i + 1) h.2
    refine ⟨by simp only [List.length_cons]; omega, fun j hj hij => ?_⟩
    rcases j with _ | j
    · have hi : Nat.beq i 0 = false := beq_ne (by simpa using hij)
      have := h.1
      rw [hi, if_neg (by simp), nth_eq] at this
      simpa using this
    · have := h2 j (by simpa using hj) (by omega)
      rw [List.getD_cons_succ, show i + (j + 1) = i + 1 + j by omega]
      exact this

theorem chkStab_of {g : Nat → Nat} (hg : ∀ k, AR (g k) (lettersData.getD k idA))
    {W : List (List Nat)} {R : List Nat} (hW : stabWords = W.toArray) (hR : repArr = R.toArray)
    (h : stabK g W R = true) : chkStab = true := by
  unfold stabK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  have hlen : R.length = 77 := by
    have e : ∀ L : List Nat, lenK L = L.length := fun L => by
      induction L with
      | nil => rfl
      | cons x L ih => exact congrArg Nat.succ ih
    rw [← e]
    exact Nat.eq_of_beq_eq_true h.1
  obtain ⟨hl, hi⟩ := stabW_spec W 0 h.2
  unfold chkStab
  rw [hW, hR, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨by simp; omega, by simp; exact hlen⟩, fun i hi77 => ?_⟩
  rw [List.mem_range] at hi77
  by_cases hi0 : i = 0
  · subst hi0
    rfl
  rw [Bool.or_eq_true]
  right
  have hh := hi i (by omega) (by omega)
  rw [Nat.zero_add] at hh
  obtain ⟨s1, s2, s3, s4⟩ := stabAt_spec hh
  have har := ar_evalW hg (W.getD i [])
  dsimp only
  rw [countP_rep hlen]
  simp only [getD_toArray]
  rw [(har.2 0 (by decide)).2, (har.2 _ s2).2, ← im_eq, ← im_eq, s1, s3]
  simp only [List.getD_eq_getElem?_getD] at s4
  simp [s4]

theorem neAny_spec {p : Nat} : ∀ {n : Nat}, neAny p n = true → ∃ j < n, im p j ≠ j
  | 0, h => absurd h (by simp [neAny])
  | n + 1, h => by
    have e : neAny p (n + 1) = if Nat.beq (im p n) n then neAny p n else true := bIf_eq _ _ _
    rw [e] at h
    by_cases hn : im p n = n
    · rw [if_pos (by simpa using hn)] at h
      obtain ⟨j, hj, hne⟩ := neAny_spec h
      exact ⟨j, by omega, hne⟩
    · exact ⟨n, by omega, hn⟩

theorem ne_idA {p : Nat} {d : Array Nat} (h : AR p d) (hn : notIdK p = true) : d ≠ idA := by
  obtain ⟨j, hj, hne⟩ := neAny_spec hn
  intro e
  apply hne
  have h1 := (h.2 j hj).2
  have h2 := (ar_idP.2 j hj).2
  rw [e] at h1
  rw [im_eq, ← h1, h2, idP_eq, pg_pidn (by decide) (by decide) hj]

theorem pow_idA {p k : Nat} {d : Array Nat} (h : AR p d)
    (hk : CFSG.KC.Over77.idK (powK p k) = true) :
    powA d k = idA := by
  have e : powK p k = idP := Nat.eq_of_beq_eq_true hk
  have := ar_powK h k
  rw [e] at this
  exact ar_eq this ar_idP

theorem chkOrder_of {p k : Nat} {d : Array Nat} (h : AR p d) (hk : ordK p k = true) :
    chkOrder d k = true := by
  unfold ordK at hk
  rw [bAnd_eq, Bool.and_eq_true] at hk
  unfold chkOrder
  rw [pow_idA h hk.2]
  simp [ne_idA h hk.1]

theorem chkOrders_of {A C S3 S4 : Nat} (hA : AR A dataS[0]!) (hC : AR C dataS[2]!)
    (h3 : AR S3 dataS[3]!) (h4 : AR S4 dataS[4]!)
    (h : (ordK A 3 && ordK C 5 && ordK S3 7 && ordK S4 11 &&
      strictB (wordK (let5 A (powK A 2) C (powK C 4)) w8Word idP)
        (fun x => notIdK (powK x 4) && CFSG.KC.Over77.idK (powK x 8))) = true) :
    chkOrders = true := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨o1, o2⟩, o3⟩, o4⟩, o5⟩ := h
  rw [strictB_eq', Bool.and_eq_true] at o5
  have har := ar_evalW (ar_let5 hA hC) w8Word
  unfold chkOrders
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨chkOrder_of hA o1, chkOrder_of hC o2⟩, chkOrder_of h3 o3⟩, chkOrder_of h4 o4⟩, ?_⟩
  rw [pow_idA har o5.2]
  exact ⟨bne_iff_ne.mpr (ne_idA (ar_powK har 4) o5.1), by simp⟩

end CFSG.KS.Prim77

end
