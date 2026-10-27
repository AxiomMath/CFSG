module

public import Certificates.Data.Kernel.SporSch.IntLines
public import CFSG.Certificates.Kernel.LocalQTCovTParse
import CFSG.Certificates.Kernel.Common.StrSplit
import CFSG.Certificates.Kernel.YModel.TextSound

public section

namespace CFSG.KC.IntLines

open CFSG.KC.LQT.Cov

theorem toInt?_nil : (String.ofList []).toInt? = none := by
  rw [String.toInt?_eq_none_iff]
  apply Bool.eq_false_iff.2
  intro h
  rw [String.isInt_iff] at h
  rcases h with h | ⟨t, ht, -⟩
  · rw [String.isNat_iff] at h
    exact h.1 rfl
  · have e := congrArg String.length ht
    have h1 : ("-" : String).length = 1 := by decide
    have h0 : (String.ofList []).length = 0 := by decide
    simp only [String.length_append, h1, h0] at e
    omega

theorem intsSK_sound : ∀ (ts : List (List Char)) (xs : List Int), intsSK ts = some xs →
    ts.filterMap (fun t => (String.ofList t).toInt?) = xs
  | [], xs, h => Option.some.inj h
  | [] :: ts, xs, h => by
    rw [List.filterMap_cons, toInt?_nil]
    exact intsSK_sound ts xs h
  | (c :: cs) :: ts, xs, h => by
    change Option.rec (motive := fun _ => Option (List Int)) none
      (fun x => Option.rec (motive := fun _ => Option (List Int)) none
        (fun xs => some (List.cons x xs)) (intsSK ts)) (intK (c :: cs)) = some xs at h
    cases hk : intK (c :: cs) with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some x =>
      rw [hk] at h
      cases hr : intsSK ts with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some ys =>
        rw [hr] at h
        rw [List.filterMap_cons, CFSG.KC.LQT.Cov.T.intK_sound hk, intsSK_sound ts ys hr]
        exact Option.some.inj h

theorem line_parse {l : List Char} {xs : List Int} (h : intsSK (tokK l) = some xs) :
    ((String.ofList l).splitOn " ").filterMap String.toInt? = xs ∧ lineInts l = xs := by
  refine ⟨?_, ?_⟩
  · rw [CFSG.KC.LQT.Cov.Parse.sp_eq, CFSG.KC.Str.splitOn_ofList, List.filterMap_map,
      ← CFSG.KC.LQT.Cov.Parse.tokK_eq]
    exact intsSK_sound _ xs h
  · unfold lineInts
    rw [h]

theorem nonEmpty_eq (l : List Char) : (!(String.ofList l).isEmpty) = nonEmpty l := by
  rw [CFSG.KC.YModel.TextSem.isEmpty_ofList]
  cases l <;> rfl

theorem lines_parse {α : Type} {cs : List Char} (h : textOK cs = true) (f : List Int → α) :
    (((String.ofList cs).splitOn "\n").filter (fun s => !s.isEmpty)).map
        (fun s => f ((s.splitOn " ").filterMap String.toInt?)) =
      (linesNE cs).map (fun l => f (lineInts l)) := by
  rw [CFSG.KC.LQT.Cov.Parse.nl_eq, CFSG.KC.Str.splitOn_ofList, ← CFSG.KC.LQT.Cov.Parse.linesK_eq,
    List.filter_map, List.map_map]
  have e : ((fun s : String => !s.isEmpty) ∘ String.ofList) = nonEmpty := funext nonEmpty_eq
  rw [e]
  unfold textOK at h
  rw [List.all_eq_true] at h
  apply List.map_congr_left
  intro l hl
  have hl' := h l hl
  cases hs : intsSK (tokK l) with
  | none => rw [hs] at hl'; exact absurd hl' (by simp)
  | some xs =>
    obtain ⟨h1, h2⟩ := line_parse hs
    simp only [Function.comp_apply]
    rw [h1, h2]

end CFSG.KC.IntLines

end
