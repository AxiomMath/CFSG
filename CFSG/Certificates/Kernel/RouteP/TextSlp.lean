module

public import Certificates.Data.Kernel.RouteP.TextSlp
public import Certificates.Data.RouteP.Y332
public import Certificates.Data.RouteP.Q0Planes
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Std.Data.String.ToNat
import Std.Data.String.ToInt

public section

namespace CFSG.KS.RouteP

open String CFSG.KC.Str CFSG.KC.RouteP
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

theorem splitPK_eq (c : Char) : ∀ (l acc : List Char),
    splitPK c l acc = List.splitOnPPrepend (· == c) l acc
  | [], acc => by rw [List.splitOnPPrepend_nil]; rfl
  | a :: t, acc => by
    unfold splitPK
    by_cases h : (a == c) = true
    · rw [if_pos h, List.splitOnPPrepend_cons_pos (p := (· == c)) h, splitPK_eq c t [],
        List.splitOnPPrepend_nil_right]
    · rw [if_neg h, List.splitOnPPrepend_cons_neg (p := (· == c)) (by simpa using h),
        splitPK_eq c t]

theorem splitK_eq (c : Char) (l : List Char) : splitK c l = l.splitOn c := by
  rw [splitK, splitPK_eq, List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend]

theorem nl_eq : ("\n" : String) = String.singleton '\n' := by rw [String.singleton_eq_ofList]

theorem sp_eq : (" " : String) = String.singleton ' ' := by rw [String.singleton_eq_ofList]

theorem startsWith_ofList (pre : String) (l : List Char) :
    (String.ofList l).startsWith pre = pre.toList.isPrefixOf l := by
  apply Bool.eq_iff_iff.mpr
  rw [String.startsWith_string_iff, toList_ofList, List.isPrefixOf_iff_prefix]

theorem isEmpty_ofList (t : List Char) : (String.ofList t).isEmpty = t.isEmpty := by
  cases t with
  | nil => rfl
  | cons c t =>
    simp only [List.isEmpty_cons]
    rw [Bool.eq_false_iff]
    intro h
    have := congrArg String.toList (String.isEmpty_iff.1 h)
    simp at this

theorem ne_underscore'' {c : Char} (h : c.isDigit = true) : c ≠ '_' := by
  rintro rfl
  exact absurd h (by decide)

theorem slice_toNat' {u : Slice} {ds : List Char} (hu : u.copy.toList = ds) (hne : ds ≠ [])
    (hd : ∀ c ∈ ds, c.isDigit = true) : u.toNat? = some (decVal ds) := by
  simp only [Slice.toNat?, Slice.isNat]
  simp only [Slice.forIn_eq_forIn_toList, Slice.foldl_eq_foldl_toList, hu]
  rw [forIn_yield (y := ((none : Option Bool), true)) ds]
  · simp only [hne, ↓reduceIte]
    split
    · exact congrArg some (foldl_congr _ _ ds 0 fun x hx n => by simp [ne_underscore'' (hd x hx)])
    · rename_i h
      exact absurd rfl h
  · intro c hc x
    simp [ne_underscore'' (hd c hc), hd c hc]
    rfl

theorem digitsL_iff {p : List Char} (h : digitsL p = true) :
    p ≠ [] ∧ ∀ c ∈ p, c.isDigit = true := by
  simp only [digitsL, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at h
  exact h

theorem toNat?_ofList' {p : List Char} (h : digitsL p = true) :
    (String.ofList p).toNat? = some (decVal p) := by
  obtain ⟨hne, hd⟩ := digitsL_iff h
  exact slice_toNat' (by rw [copy_toSlice, toList_ofList]) hne hd

theorem toInt?_ofList' {p : List Char} (h : digitsL p = true) :
    (String.ofList p).toInt? = some (decVal p : Int) := by
  rw [← String.toInt?_toSlice]
  apply String.Slice.toInt?_eq_some_of_toNat?_eq_some
  obtain ⟨hne, hd⟩ := digitsL_iff h
  exact slice_toNat' (by rw [copy_toSlice, toList_ofList]) hne hd

theorem toInt?_ofList_neg' {p : List Char} (h : digitsL p = true) :
    (String.ofList ('-' :: p)).toInt? = some (-(decVal p : Int)) := by
  rw [← String.toInt?_toSlice, String.Slice.toInt?_eq_of_eq_minus_append (t := String.ofList p)]
  · rw [toNat?_ofList' h]
    rfl
  · rw [copy_toSlice, ← toList_inj, toList_append, toList_ofList, toList_ofList]
    simp

theorem tokInt_eq {t : List Char} (h : tokIntOK t = true) :
    (fun s : String => if s.isEmpty then none else s.toInt?) (String.ofList t) = tokInt t := by
  match t, h with
  | [], _ => rfl
  | '-' :: ds, h =>
    simp only [isEmpty_ofList, List.isEmpty_cons, Bool.false_eq_true, if_false]
    exact toInt?_ofList_neg' h
  | c :: ds, h =>
    by_cases hc : c = '-'
    · subst hc
      simp only [isEmpty_ofList, List.isEmpty_cons, Bool.false_eq_true, if_false]
      exact toInt?_ofList_neg' h
    · have h' : digitsL (c :: ds) = true := by
        unfold tokIntOK at h
        split at h <;> simp_all
      have e : tokInt (c :: ds) = some (decVal (c :: ds) : Int) := by
        unfold tokInt
        split <;> simp_all
      simp only [isEmpty_ofList, List.isEmpty_cons, Bool.false_eq_true, if_false, e]
      exact toInt?_ofList' h'

theorem filterMap_congr' {α β γ : Type} (f : α → Option γ) (g : β → Option γ) (m : β → α) :
    ∀ (l : List β), (∀ x ∈ l, f (m x) = g x) → (l.map m).filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, h x (by simp),
      filterMap_congr' f g m l fun y hy => h y (by simp [hy])]

theorem prefLines_ofList (pre : String) (cs : List Char) (h : prefOKL pre.toList cs = true) :
    (((String.ofList cs).splitOn "\n").filter fun l => l.startsWith pre).toArray.map (fun l =>
      ((l.splitOn " ").drop 1).filterMap fun t => if t.isEmpty then none else t.toInt?) =
      (prefLinesL pre.toList cs).toArray := by
  rw [nl_eq, splitOn_ofList, ← splitK_eq, List.filter_map]
  unfold prefLinesL
  rw [List.map_toArray, List.map_map]
  congr 1
  have hfil : ((fun l : String => l.startsWith pre) ∘ String.ofList) =
      fun l => pre.toList.isPrefixOf l := by
    funext l
    exact startsWith_ofList pre l
  rw [hfil]
  apply List.map_congr_left
  intro l hl
  unfold prefOKL at h
  have hl' := List.all_eq_true.1 h l hl
  simp only [Function.comp, sp_eq, splitOn_ofList, ← splitK_eq, ← List.map_drop]
  exact filterMap_congr' _ _ _ _ fun t ht => tokInt_eq (List.all_eq_true.1 hl' t ht)

theorem slpLines_ofList (cs : List Char) (h : prefOKL ['L', ' '] cs = true) :
    slpLines (String.ofList cs) = (prefLinesL ['L', ' '] cs).toArray :=
  prefLines_ofList "L " cs h

theorem wordLines_ofList (pre : String) (cs : List Char) (h : prefOKL pre.toList cs = true) :
    wordLines (String.ofList cs) pre = (prefLinesL pre.toList cs).toArray :=
  prefLines_ofList pre cs h

theorem toNat?_nil : (String.ofList []).toNat? = none := by
  rw [← String.toNat?_toSlice]
  apply String.Slice.toNat?_eq_none
  rw [Bool.eq_false_iff]
  intro h
  have := (String.Slice.isNat_iff.1 h).1
  simp at this

theorem tokNat_eq {t : List Char} (h : (t.isEmpty || digitsL t) = true) :
    String.toNat? (String.ofList t) = tokNat t := by
  cases t with
  | nil => exact toNat?_nil
  | cons c ds =>
    simp only [List.isEmpty_cons, Bool.false_or] at h
    rw [toNat?_ofList' h]
    simp [tokNat]

theorem lineNums_ofList (pre : String) (skip : Nat) (cs : List Char)
    (h : lineNumsOKL pre.toList skip cs = true) :
    lineNums (String.ofList cs) pre skip = (lineNumsL pre.toList skip cs).toArray := by
  unfold lineNums lineNumsL
  unfold lineNumsOKL at h
  rw [nl_eq, splitOn_ofList, ← splitK_eq, List.find?_map]
  have hfil : ((fun l : String => l.startsWith pre) ∘ String.ofList) =
      fun l => pre.toList.isPrefixOf l := by
    funext l
    exact startsWith_ofList pre l
  rw [hfil]
  cases hf : (splitK '\n' cs).find? (fun l => pre.toList.isPrefixOf l) with
  | none => simp [hf]
  | some l =>
    rw [hf] at h
    simp only [Option.map_some, hf]
    rw [sp_eq, splitOn_ofList, ← splitK_eq, ← List.map_drop]
    congr 1
    exact filterMap_congr' _ _ _ _ fun t ht => tokNat_eq (List.all_eq_true.1 h t ht)

theorem tokNat'_eq {t : List Char} (h : tokNatOK t = true) :
    String.toNat? (String.ofList t) = tokNat' t := by
  by_cases hd : digitsL t = true
  · rw [toNat?_ofList' hd]
    simp [tokNat', hd]
  · have hn : tokNat' t = none := by simp [tokNat', hd]
    rw [hn]
    cases t with
    | nil => exact toNat?_nil
    | cons c ds =>
      unfold tokNatOK at h
      simp only [hd, Bool.false_or, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        at h
      rw [← String.toNat?_toSlice]
      apply String.Slice.toNat?_eq_none
      rw [Bool.eq_false_iff]
      intro hn'
      have := (String.Slice.isNat_iff.1 hn').2.1 c (by rw [copy_toSlice, toList_ofList]; simp)
      rcases this with h1 | h1
      · rw [h1] at h
        exact Bool.false_ne_true h.1.symm
      · exact h.2 h1

theorem y332LevelNums_ofList (cs : List Char) (h : levelOKL "LEVEL ".toList cs = true) :
    y332LevelNums (String.ofList cs) =
      ((levelNumsL "LEVEL ".toList cs).map List.toArray).toArray := by
  unfold y332LevelNums levelNumsL
  rw [nl_eq, splitOn_ofList, ← splitK_eq, List.filter_map]
  have hfil : ((fun l : String => l.startsWith "LEVEL ") ∘ String.ofList) =
      fun l => "LEVEL ".toList.isPrefixOf l := by
    funext l
    exact startsWith_ofList "LEVEL " l
  rw [hfil, List.map_toArray, List.map_map]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro l hl
  unfold levelOKL at h
  have hl' := List.all_eq_true.1 h l hl
  simp only [Function.comp]
  rw [sp_eq, splitOn_ofList, ← splitK_eq]
  congr 1
  exact filterMap_congr' _ _ _ _ fun t ht => tokNat'_eq (List.all_eq_true.1 hl' t ht)

end CFSG.KS.RouteP
