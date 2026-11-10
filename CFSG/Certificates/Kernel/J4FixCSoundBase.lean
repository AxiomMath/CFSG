
module

public import Certificates.Data.Kernel.J4FixC
public import CFSG.Certificates.Kernel.SporSch.J4SColsSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Sporadic.Schreier.J4SSylowBase

@[expose] public section

namespace CFSG.KC.J4FixC

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.KS.SporSch.C11 CFSG.KC.Enum
open CFSG.Sporadic.SmallF2.Native

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem notK_eq (b : Bool) : notK b = !b := by cases b <;> rfl

theorem nth_eq {α : Type} (d : α) : ∀ (l : List α) (i : Nat), nth d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, i + 1 => by
    change nth d l i = _
    rw [nth_eq d l i]
    rfl

theorem nth_map {α β : Type} (f : α → β) (d : α) (l : List α) (i : Nat) :
    nth (f d) (l.map f) i = f (nth d l i) := by
  rw [nth_eq, nth_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem paK_lt (p : Nat) : paK p < 2 ^ 11 := Nat.mod_lt _ (by norm_num)

theorem paK_mkP {a C : Nat} (ha : a < 2 ^ 11) : paK (mkP a C) = a := by
  change (a + C * 2048) % 2048 = a
  omega

theorem pcK_mkP {a C : Nat} (ha : a < 2 ^ 11) : pcK (mkP a C) = C := by
  change (a + C * 2048) / 2048 = C
  omega

theorem cols_bdd (P : Nat) : ∀ j < 11, (unpack11 P)[j]?.getD 0 < 2 ^ 11 := by
  intro j hj
  obtain ⟨hs, hb⟩ := unpack11_bounded P
  have h := hb j hj
  rw [getElem!_pos _ j (by omega)] at h
  rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]
  exact h

theorem appK_lt' (P a : Nat) : appK P a < 2 ^ 11 := by
  rw [← app_eq]
  exact vecMulN_lt (cols_bdd P) a

theorem colK_eq_ent (P j : Nat) : colK P j = ent 11 P j := rfl

theorem unpack11_ext {P Q : Nat} (h : ∀ j < 11, colK P j = colK Q j) : unpack11 P = unpack11 Q := by
  have hP := (unpack11_bounded P).1
  have hQ := (unpack11_bounded Q).1
  refine Array.ext (by rw [hP, hQ]) fun j h1 h2 => ?_
  have hj : j < 11 := by rwa [hP] at h1
  have e1 : (unpack11 P)[j]! = ent 11 P j := unpackW_get hj
  have e2 : (unpack11 Q)[j]! = ent 11 Q j := unpackW_get hj
  rw [getElem!_pos (unpack11 P) j h1] at e1
  rw [getElem!_pos (unpack11 Q) j h2] at e2
  rw [e1, e2, ← colK_eq_ent, ← colK_eq_ent, h j hj]

theorem colK_of_unpack {P Q : Nat} (h : unpack11 P = unpack11 Q) : ∀ j < 11, colK P j = colK Q j := by
  intro j hj
  have e1 := unpackW_get (w := 11) (m := 11) (P := P) hj
  have e2 := unpackW_get (w := 11) (m := 11) (P := Q) hj
  rw [colK_eq_ent, colK_eq_ent, ← e1, ← e2]
  exact congrArg (·[j]!) h

theorem peqK_spec {p q : Nat} (h : peqK p q = true) :
    paK p = paK q ∧ unpack11 (pcK p) = unpack11 (pcK q) := by
  unfold peqK at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, unpack11_ext fun j hj => ?_⟩
  exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h2 j hj)

theorem peqK_of {p q : Nat} (h1 : paK p = paK q) (h2 : unpack11 (pcK p) = unpack11 (pcK q)) :
    peqK p q = true := by
  unfold peqK
  rw [bAnd_eq, Bool.and_eq_true]
  refine ⟨by rw [h1]; exact Nat.beq_refl _, CFSG.KS.PackFld.allN_of_forall fun j hj => ?_⟩
  rw [colK_of_unpack h2 j hj]
  exact Nat.beq_refl _

theorem fixAllK_spec {rm MX MXI MY MYI : Nat} {eta : Nat → Nat → Nat} {v : Nat}
    {G : List (List Nat × Nat)} (h : fixAllK rm MX MXI MY MYI eta v G = true) :
    ∀ g ∈ G, g.2 < 2 ^ 11 ∧ eta (walkK rm MX MXI MY MYI g.1 v) g.2 = v := by
  induction G with
  | nil => intro g hg; simp at hg
  | cons g' G ih =>
    change bAnd(Nat.blt g'.2 2048, bAnd(_, fixAllK rm MX MXI MY MYI eta v G)) = true at h
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨Nat.le_of_ble_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1⟩
    · exact ih h.2.2 g hg

theorem distinctK_spec {L : List Nat} (h : distinctK L = true) :
    L.Pairwise fun p q => peqK p q = false := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons p t ih =>
    change bAnd(List.rec (motive := fun _ => Bool) true
      (fun q _ ih' => bAnd(notK (peqK p q), ih')) t, distinctK t) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    refine List.Pairwise.cons ?_ (ih h.2)
    have h1 := h.1
    clear h ih
    induction t with
    | nil => intro q hq; simp at hq
    | cons q t ih2 =>
      change bAnd(notK (peqK p q), _) = true at h1
      rw [bAnd_eq, Bool.and_eq_true, notK_eq, Bool.not_eq_true'] at h1
      intro q' hq'
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact h1.1
      · exact ih2 h1.2 q' hq'

theorem allRec_spec (f : Nat → Bool) : ∀ M : List Nat,
    List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(f q, ih)) M = true →
      ∀ q ∈ M, f q = true
  | [], _, q, hq => by simp at hq
  | q' :: M, h, q, hq => by
    change bAnd(f q', List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(f q, ih)) M) =
      true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1
    · exact allRec_spec f M h.2 q hq

theorem memPK_spec {p : Nat} {L : List Nat} (h : memPK p L = true) : ∃ q ∈ L, peqK p q = true := by
  induction L with
  | nil => exact absurd h Bool.false_ne_true
  | cons q t ih =>
    change bIf(peqK p q, true, memPK p t) = true at h
    cases e : peqK p q
    · rw [e] at h
      obtain ⟨q', hq', e'⟩ := ih h
      exact ⟨q', List.mem_cons_of_mem _ hq', e'⟩
    · exact ⟨q, List.mem_cons_self, e⟩

theorem closedK_spec {L : List Nat} (h : closedK L = true) :
    ∀ p ∈ L, ∀ q ∈ L, ∃ r ∈ L, peqK (pmulK p q) r = true := by
  suffices H : ∀ L' : List Nat, List.rec (motive := fun _ => Bool) true
      (fun p _ ih => bAnd(List.rec (motive := fun _ => Bool) true
        (fun q _ ih' => bAnd(memPK (pmulK p q) L, ih')) L, ih)) L' = true →
      ∀ p ∈ L', ∀ q ∈ L, memPK (pmulK p q) L = true by
    intro p hp q hq
    exact memPK_spec (H L h p hp q hq)
  intro L' hL'
  induction L' with
  | nil => intro p hp; simp at hp
  | cons p t ih =>
    change bAnd(List.rec (motive := fun _ => Bool) true
      (fun q _ ih' => bAnd(memPK (pmulK p q) L, ih')) L, _) = true at hL'
    rw [bAnd_eq, Bool.and_eq_true] at hL'
    intro p' hp'
    rcases List.mem_cons.1 hp' with rfl | hp'
    · exact allRec_spec _ L hL'.1
    · exact ih hL'.2 p' hp'

theorem commK_spec {r : Nat} {CL : List Nat} (h : commK r CL = true) :
    ∀ c ∈ CL, peqK (pmulK c r) (pmulK r c) = true := by
  induction CL with
  | nil => intro c hc; simp at hc
  | cons c t ih =>
    change bAnd(peqK (pmulK c r) (pmulK r c), commK r t) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact h.1
    · exact ih h.2 c' hc'

theorem tagK_spec {RL : List Nat} {p f t : Nat} (h : tagK RL p f t = true) :
    (t = 0 ∧ fixCntK (pcK p) ≠ 32) ∨
      ∃ r, t = r + 1 ∧ peqK (pmulK f p) (pmulK (nth pidP RL r) f) = true := by
  rcases t with _ | r
  · left
    refine ⟨rfl, fun e => ?_⟩
    change notK (Nat.beq (fixCntK (pcK p)) 32) = true at h
    rw [notK_eq, e] at h
    exact absurd h (by decide)
  · exact Or.inr ⟨r, rfl, h⟩

theorem sortedK_spec {L : List Nat} {prev : Nat} (h : sortedK L prev = true) :
    (∀ p ∈ L, canonK (pcK p) = true ∧ prev < pcK p) ∧ L.Pairwise fun p q => pcK p < pcK q := by
  induction L generalizing prev with
  | nil => exact ⟨fun p hp => by simp at hp, List.Pairwise.nil⟩
  | cons p t ih =>
    change strictB (pcK p) (fun k => bAnd(canonK k, bAnd(Nat.blt prev k, sortedK t k))) = true at h
    rw [sB, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hlt : prev < pcK p := Nat.le_of_ble_eq_true h2
    obtain ⟨ih1, ih2⟩ := ih h3
    refine ⟨fun q hq => ?_, List.Pairwise.cons (fun q hq => (ih1 q hq).2) ih2⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨h1, hlt⟩
    · exact ⟨(ih1 q hq).1, hlt.trans (ih1 q hq).2⟩

theorem foldr_cnt (f : Nat → Bool) : ∀ n s,
    (List.range n).foldr (fun a s => nIf(f a, Nat.succ s, s)) s =
      s + ((Finset.range n).filter fun a => f a = true).card
  | 0, s => by simp
  | n + 1, s => by
    rw [List.range_succ, List.foldr_append, foldr_cnt f n, Finset.range_add_one,
      Finset.filter_insert]
    simp only [List.foldr_cons, List.foldr_nil]
    cases h : f n
    · simp
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      simp only
      omega

theorem cntN_eq (n : Nat) (f : Nat → Bool) :
    cntN n f = ((Finset.range n).filter fun a => f a = true).card := by
  rw [cntN, CFSG.KC.Pack.foldN_eq, foldr_cnt, Nat.zero_add]

def PairRep (g : J) (p : ℕ) : Prop :=
  ∃ k ∈ K, g = η (paK p) * k ∧ ActsBy k (unpack11 (pcK p))

theorem letter_neg_codeL (c : ℕ) : letter x y (-(codeL c)) = (letter x y (codeL c))⁻¹ := by
  rcases c with _ | _ | _ | c <;> simp [codeL, letter]

theorem signedWord_invI (w : List ℕ) : signedWord x y (invI w) = (signedWord x y (toI w))⁻¹ := by
  induction w with
  | nil => simp [signedWord, invI, toI]
  | cons c w ih =>
    have e : invI (c :: w) = invI w ++ [-(codeL c)] := by simp [invI, toI]
    rw [e, signedWord, List.map_append, List.prod_append, ← signedWord, ih]
    simp [signedWord, toI, letter_neg_codeL]

section Gen

variable {X XI Y YI : Nat} (hX : bindWK 11 11 xColumns.toList X = true)
  (hXI : bindWK 11 11 xInvColumns.toList XI = true) (hY : bindWK 11 11 yColumns.toList Y = true)
  (hYI : bindWK 11 11 yInvColumns.toList YI = true)
include hX hXI hY hYI

end Gen

noncomputable def letE (gs : List J) (c : ℕ) : J :=
  if c % 2 = 0 then nth 1 gs (c / 2) else (nth 1 gs (c / 2))⁻¹

noncomputable def wordE (gs : List J) (w : List ℕ) : J := (w.map (letE gs)).prod

theorem wordE_cons (gs : List J) (c : ℕ) (w : List ℕ) :
    wordE gs (c :: w) = letE gs c * wordE gs w := by
  rw [wordE, wordE, List.map_cons, List.prod_cons]

theorem wordE_mem {gs : List J} {S : Subgroup J} (hS : ∀ g ∈ gs, g ∈ S) :
    ∀ w, wordE gs w ∈ S := by
  have h1 : ∀ i, nth 1 gs i ∈ S := fun i => by
    rw [nth_eq, List.getD_eq_getElem?_getD]
    cases e : gs[i]? with
    | none => exact S.one_mem
    | some g => exact hS g (List.mem_of_getElem? e)
  intro w
  refine S.list_prod_mem fun g hg => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hg
  unfold letE
  split_ifs
  · exact h1 _
  · exact S.inv_mem (h1 _)

theorem letE_inv (gs : List J) (c : ℕ) : letE gs (c + 1 - 2 * (c % 2)) = (letE gs c)⁻¹ := by
  have e : (c + 1 - 2 * (c % 2)) / 2 = c / 2 := by omega
  unfold letE
  rw [e]
  by_cases h : c % 2 = 0
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg h, inv_inv]

theorem wordE_append (gs : List J) (w w' : List ℕ) :
    wordE gs (w ++ w') = wordE gs w * wordE gs w' := by
  rw [wordE, wordE, wordE, List.map_append, List.prod_append]

theorem wordE_invW (gs : List J) (w : List ℕ) : wordE gs (invW w) = (wordE gs w)⁻¹ := by
  induction w with
  | nil => simp [wordE, invW]
  | cons c w ih =>
    have e : invW (c :: w) = invW w ++ [c + 1 - 2 * (c % 2)] := by simp [invW]
    rw [e, wordE_append, ih, wordE_cons]
    simp [wordE, letE_inv]

end CFSG.KC.J4FixC

end
