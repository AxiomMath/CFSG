module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem additive_pairing_skew {V : Type u} {C : Type v}
    [AddCommGroup V] [AddCommGroup C] (pairing : V →+ V →+ C)
    (halternating : ∀ vector, pairing vector vector = 0) (first second : V) :
    pairing first second + pairing second first = 0 := by
  have hsum := halternating (first + second)
  simp only [map_add, AddMonoidHom.add_apply,
    halternating first, halternating second, zero_add, add_zero] at hsum
  simpa only [add_comm] using hsum

theorem invariant_pairing_difference_of_fixed {V : Type u} {C : Type v}
    [AddCommGroup V] [AddCommGroup C] (pairing : V →+ V →+ C)
    (action : V →+ V)
    (hinvariant : ∀ first second, pairing (action first) (action second) = pairing first second)
    (vector fixed : V) (hfixed : action fixed = fixed) :
    pairing (action vector - vector) fixed = 0 := by
  rw [map_sub, AddMonoidHom.sub_apply, sub_eq_zero]
  simpa only [hfixed] using hinvariant vector fixed

theorem additive_mixed_difference_commute {V : Type u} [AddCommGroup V]
    (first second : V →+ V) (hcommute : first.comp second = second.comp first) (vector : V) :
    first (second vector - vector) - (second vector - vector) =
      second (first vector - vector) - (first vector - vector) := by
  have happly : first (second vector) = second (first vector) :=
    DFunLike.congr_fun hcommute vector
  rw [map_sub, map_sub, happly]
  abel

theorem invariant_alternating_pairing_mixed_difference_eq_zero
    {V : Type u} {C : Type v} [AddCommGroup V] [AddCommGroup C]
    (pairing : V →+ V →+ C) (halternating : ∀ vector, pairing vector vector = 0)
    (hnoTwo : ∀ value : C, value + value = 0 → value = 0)
    (first second : V →+ V) (hcommute : first.comp second = second.comp first)
    (hfirst : ∀ left right, pairing (first left) (first right) = pairing left right)
    (hsecond : ∀ left right, pairing (second left) (second right) = pairing left right)
    (vector : V)
    (hfixedFirst : first (second (first vector - vector) - (first vector - vector)) =
      second (first vector - vector) - (first vector - vector))
    (hfixedSecond : second (second (first vector - vector) - (first vector - vector)) =
      second (first vector - vector) - (first vector - vector)) :
    pairing (first vector - vector) (second vector - vector) = 0 := by
  let differenceFirst := first vector - vector
  let differenceSecond := second vector - vector
  let mixed := second differenceFirst - differenceFirst
  have hvectorFirst : first vector = vector + differenceFirst := by
    dsimp only [differenceFirst]
    abel
  have hvectorSecond : second vector = vector + differenceSecond := by
    dsimp only [differenceSecond]
    abel
  have hsecondFirst : second differenceFirst = differenceFirst + mixed := by
    dsimp only [mixed]
    abel
  have hfirstSecond : first differenceSecond = differenceSecond + mixed := by
    have heq := additive_mixed_difference_commute first second hcommute vector
    change first differenceSecond - differenceSecond = mixed at heq
    rw [← heq]
    abel
  have hvanishFirst : pairing differenceFirst mixed = 0 :=
    invariant_pairing_difference_of_fixed pairing first hfirst vector mixed hfixedFirst
  have hvanishSecond : pairing differenceSecond mixed = 0 :=
    invariant_pairing_difference_of_fixed pairing second hsecond vector mixed hfixedSecond
  have hrelationFirst : pairing vector mixed + pairing differenceFirst differenceSecond = 0 := by
    have hinvariance := hfirst vector differenceSecond
    rw [hvectorFirst, hfirstSecond] at hinvariance
    simp only [map_add, AddMonoidHom.add_apply, hvanishFirst, add_zero] at hinvariance
    apply (add_eq_left (a := pairing vector differenceSecond)).mp
    convert hinvariance using 1
    abel
  have hrelationSecond : pairing vector mixed + pairing differenceSecond differenceFirst = 0 := by
    have hinvariance := hsecond vector differenceFirst
    rw [hvectorSecond, hsecondFirst] at hinvariance
    simp only [map_add, AddMonoidHom.add_apply, hvanishSecond, add_zero] at hinvariance
    apply (add_eq_left (a := pairing vector differenceFirst)).mp
    convert hinvariance using 1
    abel
  have hequal : pairing differenceFirst differenceSecond = pairing differenceSecond differenceFirst :=
    add_left_cancel (hrelationFirst.trans hrelationSecond.symm)
  apply hnoTwo
  change pairing differenceFirst differenceSecond + pairing differenceFirst differenceSecond = 0
  have hskew := additive_pairing_skew pairing halternating differenceFirst differenceSecond
  rw [← hequal] at hskew
  exact hskew

end CFSG.RankThreeEvenClassification.Helpers
