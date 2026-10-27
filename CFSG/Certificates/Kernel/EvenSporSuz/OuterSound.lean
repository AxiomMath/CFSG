module

public import CFSG.Certificates.Kernel.EvenSporSuz.Sound
public import Certificates.Data.Kernel.EvenSporSuz.Outer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.OuterCheck

public section

namespace CFSG.KC.EvenSporSuz

open CFSG.EvenSporadicStandard.TwoSuz

theorem toInt?_intValK {p : List Char} (h : intTokK p = true) :
    (String.ofList p).toInt? = some (intValK p) := by
  unfold intTokK at h
  unfold intValK
  rcases Bool.or_eq_true_iff.1 h with hd | hm
  · have hne : p.head? ≠ some '-' := by
      obtain ⟨hne, hdig⟩ := digitsK_iff hd
      cases p with
      | nil => exact absurd rfl hne
      | cons c cs =>
        intro hc
        simp only [List.head?_cons, Option.some.injEq] at hc
        subst hc
        exact absurd (hdig '-' (by simp)) (by decide)
    rw [toInt?_ofList hd]
    simp [hne]
  · rw [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨h1, h2⟩ := hm
    cases p with
    | nil => simp at h1
    | cons c t =>
      simp only [List.head?_cons, Option.some.injEq] at h1
      subst h1
      simp only [List.tail_cons] at h2
      rw [toInt?_ofList_neg h2]
      simp

theorem ne_empty_comp :
    ((fun t => decide (t ≠ "")) ∘ String.ofList) = fun p : List Char => !p.isEmpty := by
  funext l
  cases l with
  | nil => rfl
  | cons c l => simpa using ofList_ne_empty (List.cons_ne_nil c l)

theorem outerParseWord_ofList (L : List Char) (h : owOK L = true) :
    outerParseWord (String.ofList L) = owK L := by
  unfold outerParseWord owK
  rw [space_eq, CFSG.KC.Str.splitOn_ofList, List.filter_map, ne_empty_comp, List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have hp' := List.mem_filter.1 hp
  have hok := List.all_eq_true.1 h p hp'.1
  cases hq : p.isEmpty
  · simp only [hq, Bool.false_or] at hok
    simp only [Function.comp, toInt?_intValK hok, Option.getD_some]
  · have h2 := hp'.2
    simp [hq] at h2

theorem lines_ofList (cs : List Char) :
    ((String.ofList cs).splitOn "\n").filter (fun l => l ≠ "") =
      (nonEmptyLines cs).map String.ofList := by
  unfold nonEmptyLines
  rw [nl_eq, CFSG.KC.Str.splitOn_ofList, List.filter_map, ne_empty_comp]

end CFSG.KC.EvenSporSuz
