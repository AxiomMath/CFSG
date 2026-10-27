module

public import Certificates.Data.Kernel.LocalComp.ExcDeriv
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcSp6Inputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8Defs
public import CFSG.Certificates.Kernel.Griess13.SLPTextSound

public section

namespace CFSG.KC.LocalComp.ExcDeriv

open String CFSG.KC.G13

theorem splitOn_colon (cs : List Char) :
    (String.ofList cs).splitOn ":" = (cs.splitOn ':').map String.ofList :=
  splitOn_one ":" ':' rfl rfl (by decide) rfl (by decide) cs

theorem splitOn_comma (cs : List Char) :
    (String.ofList cs).splitOn "," = (cs.splitOn ',').map String.ofList :=
  splitOn_one "," ',' rfl rfl (by decide) rfl (by decide) cs

theorem stepC_ok {S : List Char} (h1 : '-' ∈ S) (h2 : ',' ∈ S) (h3 : ':' ∈ S)
    (s : Nat × List Int × Nat) : OkC S (stepC s) := by
  unfold stepC
  refine intercalate_ok (sep_ok h3) ?_
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact natC_ok S _
  · refine intercalate_ok (sep_ok h2) fun m hm => ?_
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hm
    exact intC_ok h1 e
  · exact natC_ok S _

theorem derivC_ok {S : List Char} (h1 : '-' ∈ S) (h2 : ',' ∈ S) (h3 : ':' ∈ S) (h4 : ';' ∈ S)
    (d : List (Nat × List Int × Nat)) : OkC S (derivC d) :=
  intercalate_ok (sep_ok h4) fun l hl => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hl
    exact stepC_ok h1 h2 h3 s

theorem stepC_ne_nil (s : Nat × List Int × Nat) : stepC s ≠ [] := by
  unfold stepC
  simp [natC_ne_nil]

theorem toInt_empty : String.toInt? "" = none := by
  rw [String.toInt?_eq_none_iff]
  cases h : String.isInt ""
  · rfl
  · exfalso
    rcases String.isInt_iff.1 h with h1 | ⟨t, ht, -⟩
    · exact (String.isNat_iff.1 h1).1 rfl
    · have e := congrArg String.length ht
      have h1 : "-".length = 1 := rfl
      have h0 : "".length = 0 := rfl
      rw [String.length_append, h1, h0] at e
      omega

theorem parseWord (wd : List Int) :
    ((String.ofList ([','].intercalate (wd.map intC))).splitOn ",").filterMap String.toInt? =
      wd := by
  rw [splitOn_comma]
  by_cases hw : wd = []
  · subst hw
    simp only [List.map_nil, List.intercalate_nil, List.splitOn_nil, List.map_cons,
      List.map_nil]
    rw [String.ofList_nil]
    simp [toInt_empty]
  · rw [List.splitOn_intercalate ',' _ (by simpa using hw)]
    · rw [List.map_map, List.filterMap_map]
      exact (congrArg (fun f => wd.filterMap f) (funext fun e => intC_toInt e)).trans
        List.filterMap_some
    · intro l hl
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hl
      exact (intC_ok (S := ['-']) (by simp) e).not_mem rfl (by simp)

open CFSG.ComponentClassification.RankTwoClassical.ExcSp6

theorem parseStep_stepC (s : Nat × List Int × Nat) : parseStep (String.ofList (stepC s)) = s := by
  obtain ⟨m, wd, i⟩ := s
  have hw : ':' ∉ [','].intercalate (wd.map intC) :=
    (intercalate_ok (S := ['-', ',']) (sep_ok (by simp)) (fun l hl => by
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hl
      exact intC_ok (by simp) e)).not_mem rfl (by simp)
  have hm : ':' ∉ natC m := (natC_ok [] m).not_mem rfl (by simp)
  have hi : ':' ∉ natC i := (natC_ok [] i).not_mem rfl (by simp)
  unfold parseStep stepC
  rw [splitOn_colon, List.splitOn_intercalate ':' (by simp [hw, hm, hi]) (by simp)]
  simp only [List.map_cons, List.map_nil, natC_toNat, Option.getD_some]
  rw [parseWord]

theorem parseDeriv_derivC (d : List (Nat × List Int × Nat)) :
    parseDeriv (String.ofList (derivC d)) = d := by
  unfold parseDeriv
  by_cases hd : d = []
  · subst hd
    rfl
  · have hne : derivC d ≠ [] := by
      obtain ⟨s, d', rfl⟩ := List.exists_cons_of_ne_nil hd
      unfold derivC
      cases d' with
      | nil => simpa using stepC_ne_nil s
      | cons s' d' =>
        rw [List.map_cons, List.map_cons, List.intercalate_cons_cons]
        simp [stepC_ne_nil]
    have he : (String.ofList (derivC d)).isEmpty = false := by
      cases e : (String.ofList (derivC d)).isEmpty
      · rfl
      · exact absurd (String.ofList_eq_empty_iff.1 (String.isEmpty_iff.1 e)) hne
    rw [he]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold derivC
    rw [splitOn_semi, List.splitOn_intercalate ';' _ (by simpa using hd)]
    · rw [List.map_map, List.map_map]
      conv_rhs => rw [← List.map_id d]
      congr 1
      funext s
      exact parseStep_stepC s
    · intro l hl
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hl
      exact (stepC_ok (S := ['-', ',', ':']) (by simp) (by simp) (by simp) s).not_mem rfl (by simp)

theorem parseDerivs_derivsC_sp6 {ds : List (List (Nat × List Int × Nat))} (h : ds ≠ []) :
    parseDerivs (String.ofList (derivsC ds)) = ds := by
  unfold parseDerivs derivsC
  rw [splitOn_bar, List.splitOn_intercalate '|' _ (by simpa using h)]
  · rw [List.map_map, List.map_map]
    conv_rhs => rw [← List.map_id ds]
    congr 1
    funext d
    exact parseDeriv_derivC d
  · intro l hl
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hl
    exact (derivC_ok (S := ['-', ',', ':', ';']) (by simp) (by simp) (by simp) (by simp) d).not_mem
      rfl (by simp)

theorem parseDerivs_derivsC_o8 {ds : List (List (Nat × List Int × Nat))} (h : ds ≠ []) :
    CFSG.ComponentClassification.RankTwoClassical.ExcO8.parseDerivs (String.ofList (derivsC ds)) =
      ds :=
  parseDerivs_derivsC_sp6 h

end CFSG.KC.LocalComp.ExcDeriv

end
