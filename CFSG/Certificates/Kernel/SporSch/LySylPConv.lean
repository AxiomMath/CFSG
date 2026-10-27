module

public import CFSG.Certificates.Kernel.SporSch.LySylDefs
import all Init.Data.String.Legacy
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Batteries.Data.String.Lemmas
import Std.Data.String.ToInt
import Std.Data.String.ToNat
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import CFSG.Certificates.Kernel.Common.StrSplit
import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.SporSch.LyMatSound
public import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace CFSG.KS.SporSch.LySylP.Conv

open String CFSG.KC.Enum CFSG.KS.SporSch.LySyl CFSG.KS.SporSch.LyTxt

private theorem aux_step (sep : String) (p r : List Char) (c : Char) (b j : Pos.Raw)
    (acc : List String) :
    splitOnAux (ofList (p ++ c :: r)) sep b ⟨utf8Len p⟩ j acc =
      if c == j.get sep then
        (if (j.next sep).atEnd sep then
          splitOnAux (ofList (p ++ c :: r)) sep ⟨utf8Len p + c.utf8Size⟩
            ⟨utf8Len p + c.utf8Size⟩ 0
            (b.extract (ofList (p ++ c :: r))
              ((⟨utf8Len p + c.utf8Size⟩ : Pos.Raw).unoffsetBy (j.next sep)) :: acc)
        else splitOnAux (ofList (p ++ c :: r)) sep b ⟨utf8Len p + c.utf8Size⟩ (j.next sep) acc)
      else splitOnAux (ofList (p ++ c :: r)) sep b
        (((⟨utf8Len p⟩ : Pos.Raw).unoffsetBy j).next (ofList (p ++ c :: r))) 0 acc := by
  rw [splitOnAux]
  have hne : ¬ (⟨utf8Len p⟩ : Pos.Raw).atEnd (ofList (p ++ c :: r)) := by
    simp only [atEnd_iff, rawEndPos_ofList, utf8Len_append, utf8Len_cons, Pos.Raw.mk_le_mk]
    have := c.utf8Size_pos
    omega
  rw [if_neg hne, get_of_valid, next_of_valid]
  rfl

private theorem aux_end (sep : String) (p : List Char) (b j : Pos.Raw) (acc : List String) :
    splitOnAux (ofList p) sep b ⟨utf8Len p⟩ j acc =
      (b.extract (ofList p) ⟨utf8Len p⟩ :: acc).reverse := by
  rw [splitOnAux]
  have he : (⟨utf8Len p⟩ : Pos.Raw).atEnd (ofList p) := by
    simp
  rw [if_pos he]

private theorem sep_get0 : Pos.Raw.get " : " 0 = ' ' := rfl
private theorem sep_get1 : Pos.Raw.get " : " ⟨1⟩ = ':' := rfl
private theorem sep_get2 : Pos.Raw.get " : " ⟨2⟩ = ' ' := rfl
private theorem sep_next0 : Pos.Raw.next " : " 0 = ⟨1⟩ := rfl
private theorem sep_next1 : Pos.Raw.next " : " ⟨1⟩ = ⟨2⟩ := rfl
private theorem sep_next2 : Pos.Raw.next " : " ⟨2⟩ = ⟨3⟩ := rfl
private theorem sep_end1 : ¬ (⟨1⟩ : Pos.Raw).atEnd " : " := by decide
private theorem sep_end2 : ¬ (⟨2⟩ : Pos.Raw).atEnd " : " := by decide
private theorem sep_end3 : (⟨3⟩ : Pos.Raw).atEnd " : " := by decide
private theorem sp_size : (' ' : Char).utf8Size = 1 := rfl
private theorem colon_size : (':' : Char).utf8Size = 1 := rfl

private theorem split_tail : ∀ (r : List Char), (∀ c ∈ r, c ≠ ':') → ∀ (l m : List Char)
    (acc : List String),
    splitOnAux (ofList (l ++ m ++ r)) " : " ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      (ofList (m ++ r) :: acc).reverse
  | [], _, l, m, acc => by
    rw [List.append_nil, List.append_nil, (by simp : utf8Len l + utf8Len m = utf8Len (l ++ m)),
      aux_end]
    have := extract_of_valid l m []
    rw [List.append_nil, (by simp : utf8Len l + utf8Len m = utf8Len (l ++ m))] at this
    rw [this]
  | c :: r, hr, l, m, acc => by
    have e1 : l ++ m ++ c :: r = (l ++ m) ++ c :: r := rfl
    rw [e1, (by simp : utf8Len l + utf8Len m = utf8Len (l ++ m)), aux_step]
    by_cases hc : c = ' '
    · subst hc
      rw [sep_get0, sep_next0, if_pos (by decide), if_neg sep_end1, sp_size]
      cases r with
      | nil =>
        have e2 : l ++ m ++ [' '] = l ++ (m ++ [' ']) := by simp
        rw [e2, (by simp [sp_size]; omega : utf8Len (l ++ m) + 1 = utf8Len (l ++ (m ++ [' ']))),
          aux_end]
        have := extract_of_valid l (m ++ [' ']) []
        rw [List.append_nil] at this
        rw [show utf8Len (l ++ (m ++ [' '])) = utf8Len l + utf8Len (m ++ [' ']) by simp, this]
      | cons d r' =>
        have hd : d ≠ ':' := hr d (by simp)
        have e2 : l ++ m ++ ' ' :: d :: r' = (l ++ m ++ [' ']) ++ d :: r' := by simp
        rw [e2, (by simp [sp_size]; omega : utf8Len (l ++ m) + 1 = utf8Len (l ++ m ++ [' '])),
          aux_step, sep_get1, if_neg (by simpa using hd)]
        have hp : ((⟨utf8Len (l ++ m ++ [' '])⟩ : Pos.Raw).unoffsetBy ⟨1⟩) = ⟨utf8Len (l ++ m)⟩ := by
          simp [Pos.Raw.unoffsetBy, sp_size]
        rw [hp, ← e2, next_of_valid, sp_size]
        have := split_tail (d :: r') (fun x hx => hr x (by simp [hx])) l (m ++ [' ']) acc
        rw [show l ++ (m ++ [' ']) ++ d :: r' = l ++ m ++ ' ' :: d :: r' by simp,
          show utf8Len l + utf8Len (m ++ [' ']) = utf8Len (l ++ m) + 1 by simp [sp_size]; omega,
          show m ++ [' '] ++ d :: r' = m ++ ' ' :: d :: r' by simp] at this
        exact this
    · rw [if_neg (by simpa [sep_get0] using hc)]
      have hp : ((⟨utf8Len (l ++ m)⟩ : Pos.Raw).unoffsetBy 0) = ⟨utf8Len (l ++ m)⟩ := by
        simp [Pos.Raw.unoffsetBy]
      rw [hp, next_of_valid]
      have := split_tail r (fun x hx => hr x (by simp [hx])) l (m ++ [c]) acc
      rw [show l ++ (m ++ [c]) ++ r = l ++ m ++ c :: r by simp,
        show utf8Len l + utf8Len (m ++ [c]) = utf8Len (l ++ m) + c.utf8Size by simp; omega,
        show m ++ [c] ++ r = m ++ c :: r by simp] at this
      exact this

private theorem split_head : ∀ (ds : List Char), (∀ c ∈ ds, c ≠ ' ') → ∀ (w : List Char),
    (∀ c ∈ w, c ≠ ':') → ∀ (l m : List Char) (acc : List String),
    splitOnAux (ofList (l ++ m ++ (ds ++ ' ' :: ':' :: ' ' :: w))) " : " ⟨utf8Len l⟩
      ⟨utf8Len l + utf8Len m⟩ 0 acc = (ofList w :: ofList (m ++ ds) :: acc).reverse
  | [], _, w, hw, l, m, acc => by
    have e1 : l ++ m ++ ([] ++ ' ' :: ':' :: ' ' :: w) = (l ++ m) ++ ' ' :: ':' :: ' ' :: w := by
      simp
    rw [e1, (by simp : utf8Len l + utf8Len m = utf8Len (l ++ m)), aux_step, sep_get0, sep_next0,
      if_pos (by decide), if_neg sep_end1, sp_size]
    have e2 : (l ++ m) ++ ' ' :: ':' :: ' ' :: w = (l ++ m ++ [' ']) ++ ':' :: ' ' :: w := by simp
    rw [e2, (by simp [sp_size]; omega : utf8Len (l ++ m) + 1 = utf8Len (l ++ m ++ [' '])),
      aux_step, sep_get1, sep_next1, if_pos (by decide), if_neg sep_end2, colon_size]
    have e3 : (l ++ m ++ [' ']) ++ ':' :: ' ' :: w = (l ++ m ++ [' ', ':']) ++ ' ' :: w := by simp
    rw [e3, (by simp [sp_size, colon_size]; omega :
        utf8Len (l ++ m ++ [' ']) + 1 = utf8Len (l ++ m ++ [' ', ':'])),
      aux_step, sep_get2, sep_next2, if_pos (by decide), if_pos sep_end3, sp_size]
    have hp : ((⟨utf8Len (l ++ m ++ [' ', ':']) + 1⟩ : Pos.Raw).unoffsetBy ⟨3⟩) =
        ⟨utf8Len l + utf8Len m⟩ := by
      simp [Pos.Raw.unoffsetBy, sp_size, colon_size]
      omega
    have hx := extract_of_valid l m (' ' :: ':' :: ' ' :: w)
    rw [show l ++ m ++ ' ' :: ':' :: ' ' :: w = l ++ m ++ [' ', ':'] ++ ' ' :: w by simp] at hx
    rw [hp, hx]
    have := split_tail w hw (l ++ m ++ [' ', ':', ' ']) [] (ofList m :: acc)
    rw [show l ++ m ++ [' ', ':', ' '] ++ [] ++ w = l ++ m ++ [' ', ':'] ++ ' ' :: w by simp,
      show utf8Len (l ++ m ++ [' ', ':', ' ']) + utf8Len ([] : List Char) =
        utf8Len (l ++ m ++ [' ', ':']) + 1 by simp [sp_size, colon_size]; omega,
      List.nil_append] at this
    rw [show utf8Len (l ++ m ++ [' ', ':', ' ']) = utf8Len (l ++ m ++ [' ', ':']) + 1 by
      simp [sp_size, colon_size]; omega] at this
    rw [this, List.append_nil]
  | c :: ds, hds, w, hw, l, m, acc => by
    have hc : c ≠ ' ' := hds c (by simp)
    have e1 : l ++ m ++ (c :: ds ++ ' ' :: ':' :: ' ' :: w) =
        (l ++ m) ++ c :: (ds ++ ' ' :: ':' :: ' ' :: w) := by simp
    rw [e1, (by simp : utf8Len l + utf8Len m = utf8Len (l ++ m)), aux_step,
      if_neg (by simpa [sep_get0] using hc)]
    have hp : ((⟨utf8Len (l ++ m)⟩ : Pos.Raw).unoffsetBy 0) = ⟨utf8Len (l ++ m)⟩ := by
      simp [Pos.Raw.unoffsetBy]
    rw [hp, next_of_valid]
    have := split_head ds (fun x hx => hds x (by simp [hx])) w hw l (m ++ [c]) acc
    rw [show l ++ (m ++ [c]) ++ (ds ++ ' ' :: ':' :: ' ' :: w) =
        l ++ m ++ c :: (ds ++ ' ' :: ':' :: ' ' :: w) by simp,
      show utf8Len l + utf8Len (m ++ [c]) = utf8Len (l ++ m) + c.utf8Size by simp; omega,
      show m ++ [c] ++ ds = m ++ c :: ds by simp] at this
    exact this

private theorem splitOn_sep {ds w : List Char} (hds : ∀ c ∈ ds, c ≠ ' ') (hw : ∀ c ∈ w, c ≠ ':') :
    (ofList (ds ++ ' ' :: ':' :: ' ' :: w)).splitOn " : " = [ofList ds, ofList w] := by
  unfold String.splitOn
  rw [if_neg (by decide)]
  have := split_head ds hds w hw [] [] []
  simpa using this

private theorem run_cons (ch : Char) (cs : List Char) (ph v len : Nat) (ws : List Int)
    (CL : List (Nat × List Int)) : convRun (ch :: cs) ph v len ws CL =
    strictB (Char.toNat ch) (fun c =>
      bIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
        bIf(Nat.beq ph (nat_lit 0),
          strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) (fun v' =>
            strictB (Nat.succ len) (fun len' => convRun cs (nat_lit 0) v' len' ws CL)),
        bIf(bIf(Nat.beq ph (nat_lit 2), true, Nat.beq ph (nat_lit 5)),
          strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) (fun v' =>
            strictB (Nat.succ len) (fun len' => convRun cs (nat_lit 2) v' len' ws CL)),
          false)),
      bIf(Nat.beq ph (nat_lit 0),
        bAnd(Nat.beq c (nat_lit 32), bAnd(Nat.blt (nat_lit 0) len,
          List.rec (motive := fun _ => Bool) false
            (fun e _ _ => Prod.rec (motive := fun _ => Bool) (fun k w =>
              bAnd(Nat.beq k v, convRun cs (nat_lit 3) (nat_lit 0) (nat_lit 0) w CL)) e) CL)),
      bIf(Nat.beq ph (nat_lit 3), bAnd(Nat.beq c (nat_lit 58), convRun cs (nat_lit 4) v len ws CL),
      bIf(Nat.beq ph (nat_lit 4), bAnd(Nat.beq c (nat_lit 32),
          convRun cs (nat_lit 5) (nat_lit 0) (nat_lit 0) ws CL),
      bIf(Nat.beq ph (nat_lit 5), bAnd(Nat.beq c (nat_lit 10),
          bAnd(List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ws,
            List.rec (motive := fun _ => Bool) false
              (fun _ CL' _ => convRun cs (nat_lit 0) (nat_lit 0) (nat_lit 0) [] CL') CL)),
      bAnd(Nat.beq ph (nat_lit 2), bAnd(Nat.blt (nat_lit 0) len,
        List.rec (motive := fun _ => Bool) false
          (fun z rest _ => bAnd(Nat.beq (CFSG.KS.Mathieu.icode z) (Nat.add v v),
            bIf(Nat.beq c (nat_lit 32), convRun cs (nat_lit 2) (nat_lit 0) (nat_lit 0) rest CL,
              bAnd(Nat.beq c (nat_lit 10),
                bAnd(List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rest,
                  List.rec (motive := fun _ => Bool) false
                    (fun _ CL' _ => convRun cs (nat_lit 0) (nat_lit 0) (nat_lit 0) [] CL') CL)))))
          ws)))))))) := rfl

private theorem run_nil {ph v len : Nat} {ws : List Int} {CL : List (Nat × List Int)}
    (h : convRun [] ph v len ws CL = true) : ph = 0 ∧ CL = [] := by
  have e : convRun [] ph v len ws CL = (Nat.beq ph 0 && (Nat.beq ph 0 && CL.isEmpty)) := by
    cases CL <;> rfl
  rw [e] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, List.isEmpty_iff] at h
  exact ⟨h.1, h.2.2⟩

private theorem b00 : Nat.beq 0 0 = true := rfl
private theorem b20 : Nat.beq 2 0 = false := rfl
private theorem b30 : Nat.beq 3 0 = false := rfl
private theorem b40 : Nat.beq 4 0 = false := rfl
private theorem b50 : Nat.beq 5 0 = false := rfl
private theorem b22 : Nat.beq 2 2 = true := rfl
private theorem b32 : Nat.beq 3 2 = false := rfl
private theorem b42 : Nat.beq 4 2 = false := rfl
private theorem b52 : Nat.beq 5 2 = false := rfl
private theorem b33 : Nat.beq 3 3 = true := rfl
private theorem b43 : Nat.beq 4 3 = false := rfl
private theorem b53 : Nat.beq 5 3 = false := rfl
private theorem b23 : Nat.beq 2 3 = false := rfl
private theorem b44 : Nat.beq 4 4 = true := rfl
private theorem b54 : Nat.beq 5 4 = false := rfl
private theorem b24 : Nat.beq 2 4 = false := rfl
private theorem b55 : Nat.beq 5 5 = true := rfl
private theorem b25 : Nat.beq 2 5 = false := rfl
private theorem b35 : Nat.beq 3 5 = false := rfl
private theorem b45 : Nat.beq 4 5 = false := rfl

private theorem run_dig {ch : Char} {cs : List Char} {ph v len : Nat} {ws : List Int}
    {CL : List (Nat × List Int)} (hd : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = true)
    (hph : ph = 0 ∨ ph = 2 ∨ ph = 5) :
    convRun (ch :: cs) ph v len ws CL =
      convRun cs (if ph = 0 then 0 else 2) (v * 10 + (ch.toNat - 48)) (len + 1) ws CL := by
  rw [run_cons]
  simp only [strictB_eqT, bAnd_eqT]
  simp only [bIf_eqT]
  rw [if_pos hd]
  rcases hph with rfl | rfl | rfl
  · rw [if_pos b00]
    rfl
  · rw [if_neg (by simp [b20]), if_pos (by simp [b22])]
    rfl
  · rw [if_neg (by simp [b50]), if_neg (by simp [b52]), b55, Bool.true_and]
    rfl

private theorem run_dig_bad {ch : Char} {cs : List Char} {ph v len : Nat} {ws : List Int}
    {CL : List (Nat × List Int)} (hd : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = true)
    (hph : ph = 3 ∨ ph = 4) : convRun (ch :: cs) ph v len ws CL = false := by
  rw [run_cons]
  simp only [strictB_eqT, bAnd_eqT]
  simp only [bIf_eqT]
  rw [if_pos hd]
  rcases hph with rfl | rfl
  · rw [if_neg (by simp [b30])]
    simp [b32, b35]
  · rw [if_neg (by simp [b40])]
    simp [b42, b45]

private theorem run0_nd {ch : Char} {cs : List Char} {v len : Nat} {ws : List Int}
    {CL : List (Nat × List Int)} (hd : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = false)
    (h : convRun (ch :: cs) 0 v len ws CL = true) :
    ch = ' ' ∧ 0 < len ∧ ∃ w CL', CL = (v, w) :: CL' ∧ convRun cs 3 0 0 w CL = true := by
  rw [run_cons] at h
  simp only [strictB_eqT, bAnd_eqT] at h
  simp only [bIf_eqT, hd, Bool.false_eq_true, ↓reduceIte, b00] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h32, hlen, h⟩ := h
  refine ⟨char_of_beq h32 (by decide), by simpa [Nat.blt_eq] using hlen, ?_⟩
  cases CL with
  | nil => exact absurd h Bool.false_ne_true
  | cons e CL' =>
    obtain ⟨k, w⟩ := e
    simp only [Bool.and_eq_true] at h
    obtain ⟨hk, h⟩ := h
    obtain rfl := Nat.eq_of_beq_eq_true hk
    exact ⟨w, CL', rfl, h⟩

private theorem run3 {ch : Char} {cs : List Char} {v len : Nat} {ws : List Int}
    {CL : List (Nat × List Int)} (h : convRun (ch :: cs) 3 v len ws CL = true) :
    ch = ':' ∧ convRun cs 4 v len ws CL = true := by
  cases hd : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57)
  · rw [run_cons] at h
    simp only [strictB_eqT, bAnd_eqT] at h
    simp only [bIf_eqT, hd, Bool.false_eq_true, ↓reduceIte, b30, b33] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨char_of_beq h.1 (by decide), h.2⟩
  · rw [run_dig_bad hd (Or.inl rfl)] at h
    exact absurd h Bool.false_ne_true

private theorem run4 {ch : Char} {cs : List Char} {v len : Nat} {ws : List Int}
    {CL : List (Nat × List Int)} (h : convRun (ch :: cs) 4 v len ws CL = true) :
    ch = ' ' ∧ convRun cs 5 0 0 ws CL = true := by
  cases hd : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57)
  · rw [run_cons] at h
    simp only [strictB_eqT, bAnd_eqT] at h
    simp only [bIf_eqT, hd, Bool.false_eq_true, ↓reduceIte, b40, b43, b44] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨char_of_beq h.1 (by decide), h.2⟩
  · rw [run_dig_bad hd (Or.inr rfl)] at h
    exact absurd h Bool.false_ne_true

private theorem run5_nd {ch : Char} {cs : List Char} {v len : Nat} {ws : List Int}
    {CL : List (Nat × List Int)} (hd : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = false)
    (h : convRun (ch :: cs) 5 v len ws CL = true) :
    ch = '\n' ∧ ws = [] ∧ ∃ e CL', CL = e :: CL' ∧ convRun cs 0 0 0 [] CL' = true := by
  rw [run_cons] at h
  simp only [strictB_eqT, bAnd_eqT] at h
  simp only [bIf_eqT, hd, Bool.false_eq_true, ↓reduceIte, b50, b53, b54, b55] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h10, hws, h⟩ := h
  refine ⟨char_of_beq h10 (by decide), ?_, ?_⟩
  · cases ws with
    | nil => rfl
    | cons _ _ => exact absurd hws Bool.false_ne_true
  · cases CL with
    | nil => exact absurd h Bool.false_ne_true
    | cons e CL' => exact ⟨e, CL', rfl, h⟩

private theorem run2_nd {ch : Char} {cs : List Char} {v len : Nat} {ws : List Int}
    {CL : List (Nat × List Int)} (hd : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = false)
    (h : convRun (ch :: cs) 2 v len ws CL = true) :
    0 < len ∧ ∃ z rest, ws = z :: rest ∧ CFSG.KS.Mathieu.icode z = v + v ∧
      ((ch = ' ' ∧ convRun cs 2 0 0 rest CL = true) ∨
        (ch = '\n' ∧ rest = [] ∧ ∃ e CL', CL = e :: CL' ∧ convRun cs 0 0 0 [] CL' = true)) := by
  rw [run_cons] at h
  simp only [strictB_eqT, bAnd_eqT] at h
  simp only [bIf_eqT, hd, Bool.false_eq_true, ↓reduceIte, b20, b23, b24, b25, b22] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hlen, h⟩ := h
  refine ⟨by simpa [Nat.blt_eq] using hlen, ?_⟩
  cases ws with
  | nil => exact absurd h Bool.false_ne_true
  | cons z rest =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨hz, h⟩ := h
    refine ⟨z, rest, rfl, Nat.eq_of_beq_eq_true hz, ?_⟩
    by_cases h32 : Nat.beq ch.toNat 32 = true
    · rw [if_pos h32] at h
      exact Or.inl ⟨char_of_beq h32 (by decide), h⟩
    · rw [if_neg h32] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨h10, hr, h⟩ := h
      refine Or.inr ⟨char_of_beq h10 (by decide), ?_, ?_⟩
      · cases rest with
        | nil => rfl
        | cons _ _ => exact absurd hr Bool.false_ne_true
      · cases CL with
        | nil => exact absurd h Bool.false_ne_true
        | cons e CL' => exact ⟨e, CL', rfl, h⟩

private theorem icode_eq {z : Int} {v : Nat} (h : CFSG.KS.Mathieu.icode z = v + v) :
    z = (v : Int) := by
  cases z with
  | ofNat k =>
    have : k + k = v + v := h
    simp only [Int.ofNat_eq_natCast, Int.natCast_inj]
    omega
  | negSucc k =>
    have : Nat.succ (Nat.succ k + Nat.succ k) = v + v := h
    omega

private theorem ne_of_dig {ch : Char} (hd : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = true) :
    ch ≠ ':' ∧ ch ≠ '\n' ∧ ch ≠ ' ' := by
  have hdc := isDigit_of hd
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact absurd hdc (by decide)

private theorem word_inv : ∀ (cs cur : List Char) (v len : Nat) (ws : List Int)
    (CL : List (Nat × List Int)),
    (∀ c ∈ cur, c.isDigit = true) → len = cur.length → v = Nat.ofDigitChars 10 cur 0 →
    convRun cs 2 v len ws CL = true →
    ∃ wd rest, cs = wd ++ '\n' :: rest ∧ (∀ c ∈ wd, c ≠ ':' ∧ c ≠ '\n') ∧
      (List.splitOnPPrepend (· == ' ') wd cur.reverse).filterMap tv = ws ∧
      ∃ e CL', CL = e :: CL' ∧ convRun rest 0 0 0 [] CL' = true
  | [], _, _, _, _, _, _, _, _, h => absurd (run_nil h).1 (by decide)
  | ch :: cs, cur, v, len, ws, CL, hd, hl, hv, h => by
    cases hdg : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57)
    · obtain ⟨hlen, z, rest, rfl, hz, hc⟩ := run2_nd hdg h
      have hne : cur ≠ [] := by
        rintro rfl
        simp only [List.length_nil] at hl
        omega
      have htv : tv cur = some z := by
        rw [icode_eq hz, hv]
        exact tv_pos hd hne
      rcases hc with ⟨rfl, h1⟩ | ⟨rfl, rfl, e, CL', rfl, h1⟩
      · obtain ⟨wd, rest', rfl, hw, hf, he⟩ :=
          word_inv cs [] 0 0 rest CL (by simp) rfl Nat.ofDigitChars_nil.symm h1
        refine ⟨' ' :: wd, rest', rfl, ?_, ?_, he⟩
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact ⟨by decide, by decide⟩
          · exact hw c hc
        · rw [List.splitOnPPrepend_cons_pos (by decide), List.reverse_reverse, List.filterMap_cons,
            htv, ← List.splitOnPPrepend_nil_right]
          simp only [List.reverse_nil] at hf
          rw [hf]
      · refine ⟨[], cs, rfl, by simp, ?_, e, CL', rfl, h1⟩
        rw [List.splitOnPPrepend_nil, List.reverse_reverse, List.filterMap_cons, htv,
          List.filterMap_nil]
    · rw [run_dig hdg (Or.inr (Or.inl rfl)), if_neg (by decide)] at h
      obtain ⟨h1, h2, h3⟩ := ne_of_dig hdg
      obtain ⟨wd, rest, rfl, hw, hf, he⟩ := word_inv cs (cur ++ [ch]) _ _ ws CL
        (fun c hc => by
          rcases List.mem_append.1 hc with hc | hc
          · exact hd c hc
          · rw [List.mem_singleton.1 hc]
            exact isDigit_of hdg)
        (by simp [hl]) (by rw [ofDigitChars_snoc, hv]) h
      refine ⟨ch :: wd, rest, rfl, ?_, ?_, he⟩
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ⟨h1, h2⟩
        · exact hw c hc
      · rw [List.splitOnPPrepend_cons_neg (by simpa using h3)]
        simpa using hf

private theorem word5 {cs : List Char} {ws : List Int} {CL : List (Nat × List Int)}
    (h : convRun cs 5 0 0 ws CL = true) :
    ∃ wd rest, cs = wd ++ '\n' :: rest ∧ (∀ c ∈ wd, c ≠ ':' ∧ c ≠ '\n') ∧
      (List.splitOnP (· == ' ') wd).filterMap tv = ws ∧
      ∃ e CL', CL = e :: CL' ∧ convRun rest 0 0 0 [] CL' = true := by
  cases cs with
  | nil => exact absurd (run_nil h).1 (by decide)
  | cons ch cs =>
    cases hdg : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57)
    · obtain ⟨rfl, rfl, e, CL', rfl, h1⟩ := run5_nd hdg h
      refine ⟨[], cs, rfl, by simp, ?_, e, CL', rfl, h1⟩
      simp [tv_nil]
    · rw [run_dig hdg (Or.inr (Or.inr rfl)), if_neg (by decide)] at h
      obtain ⟨h1, h2, h3⟩ := ne_of_dig hdg
      obtain ⟨wd, rest, rfl, hw, hf, he⟩ := word_inv cs [ch] _ _ ws CL
        (fun c hc => by
          rw [List.mem_singleton.1 hc]
          exact isDigit_of hdg)
        rfl (by rw [← List.nil_append [ch], ofDigitChars_snoc, Nat.ofDigitChars_nil]) h
      refine ⟨ch :: wd, rest, rfl, ?_, ?_, he⟩
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ⟨h1, h2⟩
        · exact hw c hc
      · rw [List.splitOnP_eq_splitOnPPrepend, List.splitOnPPrepend_cons_neg (by simpa using h3)]
        simpa using hf

private theorem line_inv : ∀ (cs ds : List Char) (v len : Nat) (ws : List Int)
    (CL : List (Nat × List Int)),
    (∀ c ∈ ds, c.isDigit = true) → len = ds.length → v = Nat.ofDigitChars 10 ds 0 →
    convRun cs 0 v len ws CL = true →
    (CL = [] ∧ ∀ c ∈ cs, c.isDigit = true) ∨
    ∃ ds' wd rest w CL', cs = ds' ++ ' ' :: ':' :: ' ' :: (wd ++ '\n' :: rest) ∧
      (∀ c ∈ ds', c.isDigit = true) ∧ ds ++ ds' ≠ [] ∧
      CL = (Nat.ofDigitChars 10 (ds ++ ds') 0, w) :: CL' ∧ (∀ c ∈ wd, c ≠ ':' ∧ c ≠ '\n') ∧
      (List.splitOnP (· == ' ') wd).filterMap tv = w ∧ convRun rest 0 0 0 [] CL' = true
  | [], _, _, _, _, _, _, _, _, h => Or.inl ⟨(run_nil h).2, by simp⟩
  | ch :: cs, ds, v, len, ws, CL, hd, hl, hv, h => by
    cases hdg : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57)
    · obtain ⟨rfl, hlen, w, CL', rfl, h1⟩ := run0_nd hdg h
      cases cs with
      | nil => exact absurd (run_nil h1).1 (by decide)
      | cons c1 cs =>
        obtain ⟨rfl, h2⟩ := run3 h1
        cases cs with
        | nil => exact absurd (run_nil h2).1 (by decide)
        | cons c2 cs =>
          obtain ⟨rfl, h3⟩ := run4 h2
          obtain ⟨wd, rest, rfl, hw, hf, e, CL'', he, h4⟩ := word5 h3
          simp only [List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hne : ds ≠ [] := by
            rintro rfl
            simp only [List.length_nil] at hl
            omega
          refine Or.inr ⟨[], wd, rest, w, CL', by simp, by simp, by simpa using hne, ?_, hw, hf, h4⟩
          rw [List.append_nil, hv]
    · rw [run_dig hdg (Or.inl rfl), if_pos rfl] at h
      rcases line_inv cs (ds ++ [ch]) _ _ ws CL
        (fun c hc => by
          rcases List.mem_append.1 hc with hc | hc
          · exact hd c hc
          · rw [List.mem_singleton.1 hc]
            exact isDigit_of hdg)
        (by simp [hl]) (by rw [ofDigitChars_snoc, hv]) h with
        ⟨hC, hcs⟩ | ⟨ds', wd, rest, w, CL', rfl, hds', -, rfl, hw, hf, h1⟩
      · refine Or.inl ⟨hC, fun c hc => ?_⟩
        rcases List.mem_cons.1 hc with rfl | hc
        · exact isDigit_of hdg
        · exact hcs c hc
      · refine Or.inr ⟨ch :: ds', wd, rest, w, CL', by simp, ?_, by simp, by simp, hw, hf, h1⟩
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact isDigit_of hdg
        · exact hds' c hc

private theorem split_line {rest : List Char} :
    ∀ (L acc : List Char), (∀ c ∈ L, c ≠ '\n') →
      List.splitOnPPrepend (· == '\n') (L ++ '\n' :: rest) acc =
        (acc.reverse ++ L) :: List.splitOnP (· == '\n') rest
  | [], acc, _ => by
    rw [List.nil_append, List.splitOnPPrepend_cons_pos (by decide), List.append_nil]
  | c :: L, acc, hL => by
    have hc : (c == '\n') = false := by simpa using hL c (by simp)
    rw [List.cons_append, List.splitOnPPrepend_cons_neg (p := fun x => x == '\n') hc,
      split_line L (c :: acc) (fun x hx => hL x (by simp [hx]))]
    simp

private theorem main_inv (F : String → Nat × List Int)
    (hF : ∀ ds wd, (∀ c ∈ ds, c.isDigit = true) → ds ≠ [] → (∀ c ∈ wd, c ≠ ':' ∧ c ≠ '\n') →
      F (ofList (ds ++ ' ' :: ':' :: ' ' :: wd)) =
        (Nat.ofDigitChars 10 ds 0, (List.splitOnP (· == ' ') wd).filterMap tv)) :
    ∀ (CL : List (Nat × List Int)) (cs : List Char), (∀ c ∈ cs.getLast?, c = '\n') →
      convRun cs 0 0 0 [] CL = true →
      (((List.splitOnP (· == '\n') cs).map ofList).filter (· != "")).map F = CL := by
  intro CL
  induction CL with
  | nil =>
    intro cs hend h
    rcases line_inv cs [] 0 0 [] [] (by simp) rfl Nat.ofDigitChars_nil.symm h with
      ⟨-, hcs⟩ | ⟨_, _, _, _, _, _, _, _, hC, _⟩
    · have : cs = [] := by
        cases hc : cs.getLast? with
        | none => exact List.getLast?_eq_none_iff.1 hc
        | some x =>
          obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hc
          have h1 := hend x (by simp [hc])
          have h2 := hcs x (by simp)
          subst h1
          exact absurd h2 (by decide)
      subst this
      simp
    · exact absurd hC (by simp)
  | cons e CL ih =>
    intro cs hend h
    rcases line_inv cs [] 0 0 [] (e :: CL) (by simp) rfl Nat.ofDigitChars_nil.symm h with
      ⟨hC, -⟩ | ⟨ds, wd, rest, w, CL', rfl, hds, hne, hC, hw, hf, h1⟩
    · exact absurd hC (by simp)
    · simp only [List.nil_append, List.cons.injEq] at hC hne
      obtain ⟨rfl, rfl⟩ := hC
      have hL : ∀ c ∈ ds ++ ' ' :: ':' :: ' ' :: wd, c ≠ '\n' := by
        intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · rintro rfl
          exact absurd (hds _ hc) (by decide)
        · simp only [List.mem_cons] at hc
          rcases hc with rfl | rfl | rfl | hc
          · decide
          · decide
          · decide
          · exact (hw c hc).2
      rw [show ds ++ ' ' :: ':' :: ' ' :: (wd ++ '\n' :: rest) =
          (ds ++ ' ' :: ':' :: ' ' :: wd) ++ '\n' :: rest by simp,
        List.splitOnP_eq_splitOnPPrepend, split_line _ [] hL, List.reverse_nil, List.nil_append,
        List.map_cons, List.filter_cons_of_pos (by simp), List.map_cons, hF ds wd hds hne hw, hf,
        ih rest ?_ h1]
      intro c hc
      apply hend
      obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 (by simpa using hc)
      rw [show ds ++ ' ' :: ':' :: ' ' :: (wd ++ '\n' :: (ys ++ [c])) =
        (ds ++ ' ' :: ':' :: ' ' :: (wd ++ '\n' :: ys)) ++ [c] by simp, List.getLast?_concat]
      simp

private theorem decVal_eq (ds : List Char) : CFSG.KC.Str.decVal ds = Nat.ofDigitChars 10 ds 0 := by
  unfold CFSG.KC.Str.decVal
  rw [Nat.ofDigitChars_eq_foldl]
  have : (fun (n : Nat) (c : Char) => n * 10 + (c.toNat - 48)) =
      (fun (sofar : Nat) (c : Char) => 10 * sofar + (c.toNat - '0'.toNat)) := by
    funext n c
    rw [Nat.mul_comm]
    rfl
  rw [this]

open CFSG.Sporadic.LySchreier.Native in
theorem conv_sound {cs : List Char} {CL : List (Nat × List Int)}
    (hend : ∀ c ∈ cs.getLast?, c = '\n') (h : convK cs CL = true) :
    (((String.ofList cs).splitOn "\n").filter (· != "")).map (fun line =>
      match line.splitOn " : " with
      | [k, w] => (k.toNat!, parseInts w)
      | _ => (0, [])) = CL := by
  rw [splitOn_nl, List.splitOnPPrepend_nil_right]
  refine main_inv _ ?_ CL cs hend h
  intro ds wd hds hne hw
  have hsp : ∀ c ∈ ds, c ≠ ' ' := by
    rintro c hc rfl
    exact absurd (hds _ hc) (by decide)
  simp only [splitOn_sep hsp (fun c hc => (hw c hc).1)]
  rw [CFSG.KC.Str.toNat!_ofList hne hds, decVal_eq, parseInts_ofList]
  unfold pI
  rw [List.filter_eq_self.2 (fun c hc => by simpa using (hw c hc).2)]

end CFSG.KS.SporSch.LySylP.Conv

end
