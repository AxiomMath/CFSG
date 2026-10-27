module

public import Certificates.Data.Kernel.Misc.G24
public import CFSG.LieType.Multipliers.G24Data
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.Misc.Spec

open CFSG.LieType.Multipliers
open CFSG.LieType.Multipliers.G24 (letterIdx parseWord)

@[expose] def encL {m : ℕ} (l : Fin m × Bool) : ℕ := 2 * l.1.val + if l.2 then 1 else 0

@[expose] def encG {m : ℕ} (w : List (Fin m × Bool)) : List ℕ := w.map encL

@[expose] def chCode (ch : Char) : Option ℕ :=
  (letterIdx ch).map fun i => 2 * i.val + if ch.isLower then 1 else 0

@[expose] noncomputable def kCode (c : ℕ) : Option ℕ :=
  if CFSG.KC.Misc.G24.letterK c = 6 then none
  else some (2 * CFSG.KC.Misc.G24.letterK c + if CFSG.KC.Misc.G24.lowerK c = true then 1 else 0)

theorem chCode_ofNat_small : ∀ c < 128, chCode (Char.ofNat c) = kCode c := by
  decide +kernel

theorem letterK_ge {c : ℕ} (hc : 128 ≤ c) : CFSG.KC.Misc.G24.letterK c = 6 := by
  unfold CFSG.KC.Misc.G24.letterK
  have h1 : Nat.ble 97 c = true := Nat.ble_eq.mpr (by omega)
  have h2 : Nat.ble 65 (Nat.sub c 32) = true :=
    Nat.ble_eq.mpr (by show 65 ≤ c - 32; omega)
  have h3 : Nat.ble (Nat.sub c 32) 69 = false := by
    rw [Bool.eq_false_iff]
    intro h
    have := Nat.ble_eq.mp h
    change c - 32 ≤ 69 at this
    omega
  have h4 : Nat.beq (Nat.sub c 32) 71 = false := by
    rw [Bool.eq_false_iff]
    intro h
    have := Nat.eq_of_beq_eq_true h
    change c - 32 = 71 at this
    omega
  simp only [CFSG.KS.PK.letN_eq, h1, h2, h3, h4, CFSG.KS.PK.andB_eq]
  rfl

theorem ofNat_ne_char {c : ℕ} (hc : 128 ≤ c) (d : Char) (hd : d.toNat < 128) (hd0 : 0 < d.toNat) :
    Char.ofNat c ≠ d := by
  intro h
  have := congrArg Char.toNat h
  rw [Char.toNat_ofNat] at this
  split_ifs at this <;> omega

theorem letterIdx_ofNat_ge {c : ℕ} (hc : 128 ≤ c) : letterIdx (Char.ofNat c) = none := by
  have ha := ofNat_ne_char hc 'a' (by decide) (by decide)
  have hA := ofNat_ne_char hc 'A' (by decide) (by decide)
  have hb := ofNat_ne_char hc 'b' (by decide) (by decide)
  have hB := ofNat_ne_char hc 'B' (by decide) (by decide)
  have hc' := ofNat_ne_char hc 'c' (by decide) (by decide)
  have hC := ofNat_ne_char hc 'C' (by decide) (by decide)
  have hd := ofNat_ne_char hc 'd' (by decide) (by decide)
  have hD := ofNat_ne_char hc 'D' (by decide) (by decide)
  have he := ofNat_ne_char hc 'e' (by decide) (by decide)
  have hE := ofNat_ne_char hc 'E' (by decide) (by decide)
  have hg := ofNat_ne_char hc 'g' (by decide) (by decide)
  have hG := ofNat_ne_char hc 'G' (by decide) (by decide)
  simp [letterIdx, ha, hA, hb, hB, hc', hC, hd, hD, he, hE, hg, hG]

theorem chCode_ofNat (c : ℕ) : chCode (Char.ofNat c) = kCode c := by
  by_cases hc : c < 128
  · exact chCode_ofNat_small c hc
  · have hc' : 128 ≤ c := by omega
    have hk : kCode c = none := by
      unfold kCode
      rw [if_pos (letterK_ge hc')]
    rw [hk]
    unfold chCode
    rw [letterIdx_ofNat_ge hc']
    rfl

theorem parseK_cons (c : ℕ) (r : List ℕ) :
    CFSG.KC.Misc.G24.parseK (c :: r) = match kCode c with
      | none => CFSG.KC.Misc.G24.parseK r
      | some x => x :: CFSG.KC.Misc.G24.parseK r := by
  have e : CFSG.KC.Misc.G24.parseK (c :: r) = Bool.rec (motive := fun _ => List ℕ)
      (List.cons (Nat.add (Nat.mul 2 (CFSG.KC.Misc.G24.letterK c))
        (Bool.rec (motive := fun _ => Nat) 0 1 (CFSG.KC.Misc.G24.lowerK c)))
        (CFSG.KC.Misc.G24.parseK r)) (CFSG.KC.Misc.G24.parseK r)
      (Nat.beq (CFSG.KC.Misc.G24.letterK c) 6) := rfl
  rw [e]
  unfold kCode
  by_cases h : CFSG.KC.Misc.G24.letterK c = 6
  · rw [h]
    simp
  · have hb : Nat.beq (CFSG.KC.Misc.G24.letterK c) 6 = false := by
      rw [Bool.eq_false_iff]
      intro h'
      exact h (Nat.eq_of_beq_eq_true h')
    rw [hb, if_neg h]
    cases CFSG.KC.Misc.G24.lowerK c <;> rfl

theorem parseK_eq_filterMap (r : List ℕ) :
    CFSG.KC.Misc.G24.parseK r = r.filterMap kCode := by
  induction r with
  | nil => rfl
  | cons c r ih =>
    rw [parseK_cons, List.filterMap_cons, ih]
    cases kCode c <;> rfl

theorem encG_parseWord (s : String) : encG (parseWord s) = s.toList.filterMap chCode := by
  unfold encG parseWord
  rw [List.map_filterMap]
  congr 1
  funext ch
  unfold chCode
  rw [Option.map_map]
  congr 1

theorem parseK_eq (r : List ℕ) :
    CFSG.KC.Misc.G24.parseK r = encG (parseWord (String.ofList (r.map Char.ofNat))) := by
  rw [encG_parseWord, String.toList_ofList, List.filterMap_map, parseK_eq_filterMap]
  congr 1
  funext c
  exact (chCode_ofNat c).symm

theorem appN_eq (a b : List ℕ) : CFSG.KC.Misc.G24.appN a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    show x :: CFSG.KC.Misc.G24.appN a b = (x :: a) ++ b
    rw [ih]
    rfl

theorem xor_one_enc {m : ℕ} (i : Fin m) (b : Bool) :
    encL (i, !b) = encL (i, b) ^^^ 1 := by
  have key : ∀ x v : ℕ, v % 2 = (x + 1) % 2 → v / 2 = x / 2 → v = x ^^^ 1 := by
    intro x v h1 h2
    have e1 : (x ^^^ 1) % 2 = (x + 1) % 2 := Nat.xor_mod_two_eq
    have e2 : (x ^^^ 1) / 2 = x / 2 := by
      rw [Nat.xor_div_two]
      simp
    omega
  cases b
  · simp only [encL, Bool.not_false, Bool.false_eq_true, if_true, if_false, Bool.true_eq_false]
    exact key _ _ rfl (by omega)
  · simp only [encL, Bool.not_true, Bool.false_eq_true, if_true, if_false]
    exact key _ _ (by omega) (by omega)

theorem invRevK_acc (w acc : List ℕ) :
    List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
      (fun x _ ih acc => ih (List.cons (Nat.xor x 1) acc)) w acc =
      (w.map fun x => x ^^^ 1).reverse ++ acc := by
  induction w generalizing acc with
  | nil => rfl
  | cons x w ih =>
    show List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
      (fun x _ ih acc => ih (List.cons (Nat.xor x 1) acc)) w ((x ^^^ 1) :: acc) = _
    rw [ih]
    simp

theorem invRevK_eq (w : List ℕ) :
    CFSG.KC.Misc.G24.invRevK w = (w.map fun x => x ^^^ 1).reverse := by
  have := invRevK_acc w []
  rw [List.append_nil] at this
  exact this

theorem encG_invRev {m : ℕ} (w : List (Fin m × Bool)) :
    encG (FreeGroup.invRev w) = ((encG w).map fun x => x ^^^ 1).reverse := by
  unfold encG FreeGroup.invRev
  rw [List.map_reverse, List.map_map, List.map_map]
  congr 2
  funext l
  exact xor_one_enc l.1 l.2

theorem commK_enc {m : ℕ} (u v : List (Fin m × Bool)) :
    CFSG.KC.Misc.G24.commK (encG u) (encG v) = encG (commWord u v) := by
  unfold CFSG.KC.Misc.G24.commK commWord
  rw [appN_eq, appN_eq, appN_eq, invRevK_eq, invRevK_eq, ← encG_invRev, ← encG_invRev]
  unfold encG
  simp [List.map_append, List.append_assoc]

theorem commsK_eq (ps : List (List ℕ × List ℕ)) :
    CFSG.KC.Misc.G24.commsK ps = encG (commWords (ps.map fun p =>
      (parseWord (String.ofList (p.1.map Char.ofNat)),
        parseWord (String.ofList (p.2.map Char.ofNat)))) : List (Fin 6 × Bool)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨u, v⟩ := p
    show CFSG.KC.Misc.G24.appN (CFSG.KC.Misc.G24.commK (CFSG.KC.Misc.G24.parseK u)
      (CFSG.KC.Misc.G24.parseK v)) (CFSG.KC.Misc.G24.commsK ps) = _
    rw [appN_eq, ih, parseK_eq, parseK_eq, commK_enc]
    simp only [commWords, List.map_cons, List.flatten_cons, encG, List.map_append]

theorem nthV_eq (l : List ℕ) (i : ℕ) : CFSG.KC.Misc.G24.nthV l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      show CFSG.KC.Misc.G24.nthV xs j = (x :: xs).getD (j + 1) 0
      rw [List.getD_cons_succ, ih j]

theorem nthL_eq (L : List (List ℕ)) (i : ℕ) : CFSG.KC.Misc.G24.nthL L i = L.getD i [] := by
  induction L generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      show CFSG.KC.Misc.G24.nthL xs j = (x :: xs).getD (j + 1) []
      rw [List.getD_cons_succ, ih j]

theorem nthLL_eq (L : List (List (List ℕ))) (i : ℕ) :
    CFSG.KC.Misc.G24.nthLL L i = L.getD i [] := by
  induction L generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      show CFSG.KC.Misc.G24.nthLL xs j = (x :: xs).getD (j + 1) []
      rw [List.getD_cons_succ, ih j]

theorem nthP_eq (L : List (List (List ℕ × List ℕ))) (i : ℕ) :
    CFSG.KC.Misc.G24.nthP L i = L.getD i [] := by
  induction L generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      show CFSG.KC.Misc.G24.nthP xs j = (x :: xs).getD (j + 1) []
      rw [List.getD_cons_succ, ih j]

theorem listRec_app {α : Type} (b a : List α) :
    List.rec (motive := fun _ => List α → List α) (fun a => a)
      (fun x _ ih a => List.cons x (ih a)) b a = b ++ a := by
  induction b generalizing a with
  | nil => rfl
  | cons x b ih =>
    show x :: List.rec (motive := fun _ => List α → List α) (fun a => a)
      (fun x _ ih a => List.cons x (ih a)) b a = _
    rw [ih]
    rfl

theorem listRec_map {α β : Type} (f : α → β) (l : List α) :
    List.rec (motive := fun _ => List β) List.nil (fun r _ ih => List.cons (f r) ih) l =
      l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show f x :: List.rec (motive := fun _ => List β) List.nil
      (fun r _ ih => List.cons (f r) ih) l = _
    rw [ih]
    rfl

theorem natRec_flat {α : Type} (f : ℕ → List α) (m : ℕ) :
    Nat.rec (motive := fun _ => List α) List.nil (fun i acc =>
      List.rec (motive := fun _ => List α → List α) (fun a => a)
        (fun x _ ih a => List.cons x (ih a)) acc (f i)) m = (List.range m).flatMap f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show List.rec (motive := fun _ => List α → List α) (fun a => a)
      (fun x _ ih a => List.cons x (ih a))
      (Nat.rec (motive := fun _ => List α) List.nil (fun i acc =>
        List.rec (motive := fun _ => List α → List α) (fun a => a)
          (fun x _ ih a => List.cons x (ih a)) acc (f i)) m) (f m) = _
    rw [ih, listRec_app]
    simp [List.range_succ, List.flatMap_append]

theorem range_six_eq : List.range 6 = (List.finRange 6).map (fun i : Fin 6 => i.val) := by
  rfl

theorem flatMap_singleton_eq {α β : Type} (f : α → β) (l : List α) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem coverK_eq (RS : List (List ℕ)) (PS : List (List (List ℕ × List ℕ))) :
    CFSG.KC.Misc.G24.coverK RS PS =
      (coverWords (m := 6) (RS.map fun r => parseWord (String.ofList (r.map Char.ofNat)))
        fun i => commWords ((PS.getD i.val []).map fun p =>
          (parseWord (String.ofList (p.1.map Char.ofNat)),
            parseWord (String.ofList (p.2.map Char.ofNat))))).map encG := by
  unfold CFSG.KC.Misc.G24.coverK
  rw [listRec_app, natRec_flat, natRec_flat]
  unfold coverWords
  rw [List.map_append, List.map_flatMap, List.map_map, range_six_eq, List.flatMap_map,
    List.flatMap_map]
  congr 1
  · refine List.flatMap_congr fun a _ => ?_
    rw [listRec_map, List.map_map, List.map_map]
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp_apply]
    rw [parseK_eq]
    have e : ([Nat.add (Nat.mul 2 a.val) 1] : List ℕ) = encG [(a, true)] := by
      simp [encG, encL]
    rw [e, commK_enc]
  · rw [flatMap_singleton_eq]
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply, encG, List.map_cons, encL, if_false]
    rw [nthP_eq, commsK_eq]
    simp [encG]

end CFSG.KC.Misc.Spec

end
