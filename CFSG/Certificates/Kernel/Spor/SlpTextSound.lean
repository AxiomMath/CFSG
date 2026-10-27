module

public import Certificates.Data.Kernel.Spor.SlpText
public import CFSG.Certificates.Kernel.Spor.SlpMatSound
public import CFSG.Certificates.Kernel.Griess13.SLPTextSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenInputs
import all Init.Data.String.Slice
import all Init.Data.String.Search

public section

namespace CFSG.KC.SlpM

open CFSG.KC.G13 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative

theorem slice_toNat!_of {s : String.Slice} {n : Nat} (h : s.toNat? = some n) : s.toNat! = n := by
  have hn := String.Slice.isNat_of_toNat?_eq_some h
  unfold String.Slice.toNat? at h
  unfold String.Slice.toNat!
  rw [if_pos hn] at h ⊢
  exact Option.some.inj h

theorem toNat!_natC (n : Nat) : (String.ofList (natC n)).toNat! = n := by
  unfold String.toNat!
  apply slice_toNat!_of
  rw [String.toNat?_toSlice]
  exact natC_toNat n

theorem splitOn_comma' (cs : List Char) :
    (String.ofList cs).splitOn "," = (cs.splitOn ',').map String.ofList :=
  splitOn_one "," ',' rfl rfl (by decide) rfl (by decide) cs

theorem natC_cons (n : Nat) : ∃ d ds, natC n = d :: ds ∧ d ≠ '-' := by
  obtain ⟨d, ds, e⟩ : ∃ d ds, natC n = d :: ds := by
    cases h : natC n with
    | nil => exact absurd h (natC_ne_nil n)
    | cons d ds => exact ⟨d, ds, rfl⟩
  refine ⟨d, ds, e, fun hd => ?_⟩
  have := (natC_ok [] n).not_mem (c := '-') (by decide) (by simp)
  rw [e, hd] at this
  exact this List.mem_cons_self

theorem codeC_odd {c : Nat} (h : c % 2 = 1) : codeC c = '-' :: natC (c / 2) := by
  have h1 : Nat.land c 1 = 1 := by change c &&& 1 = 1; rw [Nat.and_one_is_mod]; exact h
  have h2 : Nat.shiftRight c 1 = c / 2 := by change c >>> 1 = _; rw [Nat.shiftRight_eq_div_pow]
  unfold codeC
  rw [h1, h2]
  rfl

theorem codeC_even {c : Nat} (h : c % 2 = 0) : codeC c = natC (c / 2) := by
  have h1 : Nat.land c 1 = 0 := by change c &&& 1 = 0; rw [Nat.and_one_is_mod]; exact h
  have h2 : Nat.shiftRight c 1 = c / 2 := by change c >>> 1 = _; rw [Nat.shiftRight_eq_div_pow]
  unfold codeC
  rw [h1, h2]
  rfl

theorem copy_drop_one (cs : List Char) :
    ((String.ofList ('-' :: cs)).drop 1).copy = String.ofList cs := by
  apply String.ext
  rw [String.toList_copy_drop, String.toList_ofList, String.toList_ofList]
  rfl

theorem parseInt_codeC (c : Nat) : parseInt (String.ofList (codeC c)) = decC c := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [codeC_even h]
    obtain ⟨d, ds, e, hd⟩ := natC_cons (c / 2)
    have hd' : ¬'-' = d := fun h' => hd h'.symm
    have hs : (String.ofList (natC (c / 2))).startsWith "-" = false := by
      rw [e]
      simp [String.startsWith_string_iff, hd']
    unfold parseInt
    rw [hs, if_neg (by simp), toNat!_natC]
    unfold decC
    rw [if_neg (by omega)]
    rfl
  · rw [codeC_odd h]
    have hs : (String.ofList ('-' :: natC (c / 2))).startsWith "-" = true := by
      simp [String.startsWith_string_iff]
    unfold parseInt
    rw [if_pos hs]
    unfold decC
    rw [if_pos h]
    congr 2
    apply slice_toNat!_of
    rw [← String.Slice.toNat?_copy, copy_drop_one]
    exact natC_toNat _

theorem codeC_ok (c : Nat) : OkC ['-'] (codeC c) := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [codeC_even h]
    exact natC_ok _ _
  · rw [codeC_odd h]
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inr List.mem_cons_self
    · exact natC_ok _ _ x hx

theorem codeC_ne_nil (c : Nat) : codeC c ≠ [] := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [codeC_even h]
    exact natC_ne_nil _
  · rw [codeC_odd h]
    exact List.cons_ne_nil _ _

theorem wordC_ok (w : List Nat) : OkC ['-', ','] (wordC w) :=
  intercalate_ok (sep_ok (by simp)) fun l hl => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
    exact (codeC_ok c).mono (by simp)

theorem wordC_eq_nil {w : List Nat} : wordC w = [] ↔ w = [] := by
  constructor
  · intro h
    cases w with
    | nil => rfl
    | cons c w =>
      exfalso
      unfold wordC at h
      rw [List.map_cons] at h
      cases w with
      | nil => simp [codeC_ne_nil] at h
      | cons c' w => simp [List.intercalate_cons_cons, codeC_ne_nil] at h
  · rintro rfl
    rfl

theorem parse_wordC (w : List Nat) :
    (if (String.ofList (wordC w)).isEmpty = true then []
      else ((String.ofList (wordC w)).splitOn ",").map parseInt) = decW w := by
  by_cases hw : w = []
  · subst hw
    rfl
  · have hne : (String.ofList (wordC w)).isEmpty = false := by
      rw [String.isEmpty_eq_false_iff, Ne, String.ofList_eq_empty_iff, wordC_eq_nil]
      exact hw
    rw [hne, if_neg (by simp), splitOn_comma', wordC, List.splitOn_intercalate ',' (fun l hl => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
        exact (codeC_ok c).not_mem (by decide) (by simp)) (by simpa using hw),
      List.map_map, List.map_map]
    unfold decW
    congr 1
    funext c
    exact parseInt_codeC c

theorem parseIntLists_wordsC {W : List (List Nat)} (hW : W ≠ []) :
    parseIntLists (String.ofList (wordsC W)) = (W.map decW).toArray := by
  unfold parseIntLists wordsC
  rw [splitOn_semi, List.splitOn_intercalate ';' (fun l hl => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
      exact (wordC_ok w).not_mem (by decide) (by simp)) (by simpa using hW),
    List.map_map, List.map_toArray, List.map_map]
  congr 2
  funext w
  exact parse_wordC w

theorem natsC_ok (l : List Nat) : OkC [','] ([','].intercalate (l.map natC)) :=
  intercalate_ok (sep_ok (by simp)) fun m hm => by
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hm
    exact natC_ok _ n

theorem parse_pairC (p : Nat × List Nat) :
    (match (String.ofList (pairC p)).splitOn "|" with
      | [a, b] => (a.toNat!, if b.isEmpty = true then [] else (b.splitOn ",").map String.toNat!)
      | _ => (0, [])) = p := by
  obtain ⟨a, l⟩ := p
  have ha : '|' ∉ natC a := (natC_ok [] a).not_mem (by decide) (by simp)
  have hl : '|' ∉ [','].intercalate (l.map natC) := (natsC_ok l).not_mem (by decide) (by simp)
  have e : pairC (a, l) = ['|'].intercalate [natC a, [','].intercalate (l.map natC)] := by
    simp [pairC, List.intercalate_cons_cons]
  rw [e, splitOn_bar, pieces2 ha hl]
  simp only [List.map_cons, List.map_nil, toNat!_natC]
  by_cases hl0 : l = []
  · subst hl0
    simp
  · have hne : (String.ofList ([','].intercalate (l.map natC))).isEmpty = false := by
      rw [String.isEmpty_eq_false_iff, Ne, String.ofList_eq_empty_iff]
      intro h
      cases l with
      | nil => exact hl0 rfl
      | cons n l =>
        cases l with
        | nil => simp [natC_ne_nil] at h
        | cons n' l => simp [List.intercalate_cons_cons, natC_ne_nil] at h
    rw [hne, if_neg (by simp), splitOn_comma', List.splitOn_intercalate ',' (fun m hm => by
        obtain ⟨n, -, rfl⟩ := List.mem_map.1 hm
        exact (natC_ok [] n).not_mem (by decide) (by simp)) (by simpa using hl0),
      List.map_map, List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id l]
    congr 1
    funext n
    exact toNat!_natC n

theorem parsePairs_pairsC {P : List (Nat × List Nat)} (hP : P ≠ []) :
    parsePairs (String.ofList (pairsC P)) = P.toArray := by
  unfold parsePairs pairsC
  rw [splitOn_semi, List.splitOn_intercalate ';' (fun l hl => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hl
      have : OkC ['|', ','] (pairC p) := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact natC_ok _ _ x hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inr List.mem_cons_self
          · exact ((natsC_ok p.2).mono (by simp)) x hx
      exact this.not_mem (by decide) (by simp)) (by simpa using hP),
    List.map_map, List.map_toArray, List.map_map]
  conv_rhs => rw [← List.map_id P]
  congr 2
  funext p
  exact parse_pairC p

end CFSG.KC.SlpM

end
