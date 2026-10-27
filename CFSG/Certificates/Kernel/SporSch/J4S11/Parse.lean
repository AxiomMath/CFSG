module

public import Certificates.Data.Kernel.SporSch.J4S11
public import CFSG.Sporadic.Schreier.J4SElevenData
public import CFSG.Certificates.Kernel.Common.StrSplit
public import Certificates.Data.Kernel.SporSch.J4SPairK

public section

namespace CFSG.KS.SporSch.J4E.ParsePf

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ
open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

private theorem splitK_ne_nil (c : Char) : ∀ cs : List Char, splitK c cs ≠ []
  | [] => by simp [splitK]
  | x :: xs => by
    have := splitK_ne_nil c xs
    unfold splitK
    split_ifs
    · simp
    · cases h : splitK c xs
      · exact absurd h this
      · simp

private theorem splitK_eq (c : Char) : ∀ cs : List Char, splitK c cs = cs.splitOn c
  | [] => by simp [splitK, List.splitOn_nil]
  | x :: xs => by
    rw [List.splitOn_cons_eq_ite_modifyHead, ← splitK_eq c xs]
    by_cases hx : x = c
    · subst hx; simp [splitK]
    · have hx' : (x == c) = false := by simpa using hx
      rw [hx']
      simp only [splitK, hx, if_false, Bool.false_eq_true]
      cases h : splitK c xs
      · exact absurd h (splitK_ne_nil c xs)
      · rfl

private theorem digitsK_eq {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) :
    ∀ acc, digitsK ds acc = some (Nat.ofDigitChars 10 ds acc) := by
  induction ds with
  | nil => intro acc; simp [digitsK, Nat.ofDigitChars_eq_foldl]
  | cons x xs ih =>
    intro acc
    have hx := hd x (by simp)
    simp only [digitsK, hx, if_true, Nat.ofDigitChars_eq_foldl, List.foldl_cons]
    have := ih (fun c hc => hd c (by simp [hc])) (10 * acc + (x.toNat - 48))
    simpa [Nat.ofDigitChars_eq_foldl] using this

private theorem filter_digits {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) :
    ds.filter (· != '_') = ds := by
  refine List.filter_eq_self.2 fun c hc => ?_
  have h := hd c hc
  have : c ≠ '_' := by
    rintro rfl
    exact absurd h (by decide)
  simpa using this

private theorem toNat?_digits {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) :
    (String.ofList ds).toNat? = some (Nat.ofDigitChars 10 ds 0) := by
  have hn : (String.ofList ds).isNat = true :=
    String.isNat_of_isDigit (by simpa using hne) (by simpa using hd)
  rw [String.toNat?_eq_some_ofDigitChars hn, String.toList_ofList, filter_digits hd]

private theorem digitsK_some {ds : List Char} {n : Nat} (h : digitsK ds 0 = some n) :
    ∀ c ∈ ds, c.isDigit = true := by
  have : ∀ (ds : List Char) (acc : Nat), digitsK ds acc = some n → ∀ c ∈ ds, c.isDigit = true := by
    intro ds
    induction ds with
    | nil => intro acc _ c hc; simp at hc
    | cons x xs ih =>
      intro acc h c hc
      unfold digitsK at h
      by_cases hx : x.isDigit = true
      · rcases List.mem_cons.1 hc with rfl | hc
        · exact hx
        · rw [if_pos hx] at h
          exact ih _ h c hc
      · rw [if_neg hx] at h
        cases h
  exact this ds 0 h

private theorem natK_toNat {l : List Char} {n : Nat} (h : natK l = some n) :
    (String.ofList l).toNat? = some n := by
  cases l with
  | nil => simp [natK] at h
  | cons x xs =>
    have h' : digitsK (x :: xs) 0 = some n := h
    have hd := digitsK_some h'
    rw [digitsK_eq hd] at h'
    rw [toNat?_digits hd (by simp)]
    exact h'

private theorem ofList_inj {a b : List Char} (h : String.ofList a = String.ofList b) : a = b := by
  simpa using congrArg String.toList h

private theorem isEmpty_ofList (t : List Char) : (String.ofList t).isEmpty = t.isEmpty := by
  cases t <;> simp [String.isEmpty_iff]

private theorem mu_eq : "mu" = String.ofList ['m', 'u'] := by decide
private theorem iv_eq : "iv" = String.ofList ['i', 'v'] := by decide
private theorem pwr_eq : "pwr" = String.ofList ['p', 'w', 'r'] := by decide

private theorem line_sound (ts : List (List Char)) (o : Option (List Nat))
    (h : lineK ts = some o) :
    (slpLine (ts.map String.ofList)).map (Option.map instrCode) = some o := by
  rcases ts with _ | ⟨t, tail⟩
  · simp [lineK, slpLine] at h ⊢
    exact h
  · by_cases hmu : ∃ i j k, t = ['m', 'u'] ∧ tail = [i, j, k]
    · obtain ⟨i, j, k, rfl, rfl⟩ := hmu
      simp only [lineK] at h
      cases hi : natK i <;> cases hj : natK j <;> cases hk : natK k <;>
        simp [hi, hj, hk] at h
      subst h
      simp only [List.map_cons, List.map_nil, mu_eq, slpLine, natK_toNat hi, natK_toNat hj,
        natK_toNat hk]
      rfl
    by_cases hiv : ∃ i k, t = ['i', 'v'] ∧ tail = [i, k]
    · obtain ⟨i, k, rfl, rfl⟩ := hiv
      simp only [lineK] at h
      cases hi : natK i <;> cases hk : natK k <;> simp [hi, hk] at h
      subst h
      simp only [List.map_cons, List.map_nil, iv_eq, slpLine, natK_toNat hi, natK_toNat hk]
      rfl
    by_cases hpw : ∃ e i k, t = ['p', 'w', 'r'] ∧ tail = [e, i, k]
    · obtain ⟨e, i, k, rfl, rfl⟩ := hpw
      simp only [lineK] at h
      cases he : natK e <;> cases hi : natK i <;> cases hk : natK k <;>
        simp [he, hi, hk] at h
      subst h
      simp only [List.map_cons, List.map_nil, pwr_eq, slpLine, natK_toNat he, natK_toNat hi,
        natK_toNat hk]
      rfl
    rw [lineK.eq_5 t tail (fun i j k a b => hmu ⟨i, j, k, a, b⟩) (fun i k a b => hiv ⟨i, k, a, b⟩)
      (fun e i k a b => hpw ⟨e, i, k, a, b⟩)] at h
    by_cases hh : t.head? = some '#'
    · rw [if_pos hh] at h
      cases h
      obtain ⟨t', rfl⟩ : ∃ t', t = '#' :: t' := by
        cases t with
        | nil => simp at hh
        | cons x xs => simp at hh; exact ⟨xs, by rw [hh]⟩
      rw [List.map_cons, slpLine.eq_5]
      · simp
      · intro i j k a _
        exact absurd (ofList_inj (a.trans mu_eq)) (by simp)
      · intro i k a _
        exact absurd (ofList_inj (a.trans iv_eq)) (by simp)
      · intro e i k a _
        exact absurd (ofList_inj (a.trans pwr_eq)) (by simp)
    · rw [if_neg hh] at h
      cases h

private theorem mapM_sound {L : List (List Char)} {os : List (Option (List Nat))}
    (h : L.mapM (fun l => lineK ((splitK ' ' l).filter fun t => !t.isEmpty)) = some os) :
    ∃ is : List (Option Instr),
      (L.map String.ofList).mapM (fun l => slpLine (slpTokens l)) = some is ∧
      is.map (Option.map instrCode) = os := by
  induction L generalizing os with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨[], by simp, rfl⟩
  | cons l L ih =>
    rw [List.mapM_cons] at h
    obtain ⟨o, ho, os', hos, rfl⟩ : ∃ o, lineK ((splitK ' ' l).filter fun t => !t.isEmpty) = some o ∧
        ∃ os', L.mapM (fun l => lineK ((splitK ' ' l).filter fun t => !t.isEmpty)) = some os' ∧
          os = o :: os' := by
      cases ho : lineK ((splitK ' ' l).filter fun t => !t.isEmpty) with
      | none => rw [ho] at h; simp at h
      | some o =>
        rw [ho] at h
        cases hr : L.mapM (fun l => lineK ((splitK ' ' l).filter fun t => !t.isEmpty)) with
        | none => rw [hr] at h; simp at h
        | some os' => rw [hr] at h; simp at h; exact ⟨o, rfl, os', rfl, h.symm⟩
    obtain ⟨is, his, hmap⟩ := ih hos
    have hl := line_sound _ _ ho
    have htok : slpTokens (String.ofList l) =
        (((splitK ' ' l).filter fun t => !t.isEmpty)).map String.ofList := by
      unfold slpTokens
      rw [show (" " : String) = String.singleton ' ' by decide,
        CFSG.KC.Str.splitOn_ofList, ← splitK_eq, List.filter_map]
      congr 1
      refine List.filter_congr fun t _ => ?_
      simp [Function.comp, isEmpty_ofList]
    obtain ⟨i, hi, rfl⟩ : ∃ i, slpLine (((splitK ' ' l).filter fun t => !t.isEmpty).map
        String.ofList) = some i ∧ i.map instrCode = o := by
      cases hs : slpLine (((splitK ' ' l).filter fun t => !t.isEmpty).map String.ofList) with
      | none => rw [hs] at hl; simp at hl
      | some i => rw [hs] at hl; exact ⟨i, rfl, by simpa using hl⟩
    refine ⟨i :: is, ?_, by simp [hmap]⟩
    rw [List.map_cons, List.mapM_cons, htok, hi, his]
    rfl

private theorem filterMap_map (is : List (Option Instr)) :
    (is.filterMap id).map instrCode = (is.map (Option.map instrCode)).filterMap id := by
  induction is with
  | nil => rfl
  | cons i is ih => cases i <;> simp_all

theorem parseK_sound' {cs : List Char} {codes : List (List Nat)} (h : parseK cs = some codes) :
    (parseSLP (String.ofList cs)).map (List.map instrCode) = some codes := by
  unfold parseK at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨os, hos, rfl⟩ := h
  obtain ⟨is, his, hmap⟩ := mapM_sound hos
  unfold parseSLP
  rw [show ("\n" : String) = String.singleton '\n' by decide, CFSG.KC.Str.splitOn_ofList,
    ← splitK_eq]
  rw [his]
  subst hmap
  exact congrArg some (filterMap_map is)

end CFSG.KS.SporSch.J4E.ParsePf

end
