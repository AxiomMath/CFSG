module

public import CFSG.Certificates.Kernel.Co2ElevenSnd.Tree

public section

namespace CFSG.KC.Co2Eleven.Snd

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.PK CFSG.KS.TW CFSG.KC.Co2Eleven

private theorem arr_getD' (a : Array Nat) (i : Nat) : a[i]! = a.toList.getD i 0 := by
  rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

private theorem tupleEq_eq (a b : Array Nat) : tupleEq a b = decide (a.toList = b.toList) := by
  rw [Bool.eq_iff_iff, tupleEq_iff, decide_eq_true_iff, Array.toList_inj]
  constructor
  · rintro ⟨hs, ht⟩
    apply Array.ext hs
    intro t h1 h2
    have := ht t h2
    rwa [getElem!_pos a t h1, getElem!_pos b t h2] at this
  · rintro rfl
    exact ⟨rfl, fun t _ => rfl⟩

private theorem sift_step {trees : Array Tree} {letters : Array Table} {m : Nat}
    {base : Array Nat} {l : Nat} (hl : l < trees.size) (hlm : l < m) (img : Array Nat) :
    sift trees letters (Array.range m) base l img =
      (decide (ap trees[l]!.pos (img.toList.getD l 0) < trees[l]!.pts.size) &&
        sift trees letters (Array.range m) base (l + 1)
          (walkInv trees[l]! letters (ap trees[l]!.pos (img.toList.getD l 0)) img)) := by
  rw [sift.eq_def, dif_pos hl]
  have hqb : (Array.range m)[l]! = l := by
    rw [getElem!_pos _ l (by simpa using hlm), Array.getElem_range]
  have htl : trees[l] = trees[l]! := (getElem!_pos trees l hl).symm
  simp only [hqb, htl, arr_getD' img]

theorem sift_eq {trees : Array Tree} {letters : Array Table} {LC R : Nat → Nat}
    {base : Array Nat} {szs : List Nat} {m : Nat} (hsz : trees.size = m)
    (hT : ∀ l < m, TreeRec trees[l]! letters LC R l (szs.getD l 0)) :
    ∀ d l (img : Array Nat), l + d = m → (∀ x ∈ img.toList, x < 2300) →
      sift trees letters (Array.range m) base l img =
        siftL LC R base.toList szs (List.range' l d) img.toList
  | 0, l, img, hd, _ => by
    rw [sift.eq_def, dif_neg (by omega)]
    exact tupleEq_eq img base
  | d + 1, l, img, hd, hq => by
    have hlm : l < m := by omega
    rw [sift_step (by omega) hlm img]
    have H := hT l hlm
    have hx : img.toList.getD l 0 < 2300 := by
      by_cases hli : l < img.toList.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hli, Option.getD_some]
        exact hq _ (List.getElem_mem hli)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        decide
    show _ = (decide (rf R l 3 (img.toList.getD l 0) < szs.getD l 0) &&
      siftL LC R base.toList szs (List.range' (l + 1) d)
        (wiK LC R l 2300 (rf R l 3 (img.toList.getD l 0)) img.toList))
    by_cases hk : rf R l 3 (img.toList.getD l 0) < szs.getD l 0
    · have hpe := H.pos_eq _ hx hk
      obtain ⟨hw1, hw2⟩ := walkInv_eq H 2300 _ (by have := H.le; omega) hk img hq
      rw [hpe, H.size, decide_eq_true hk, Bool.true_and, Bool.true_and,
        sift_eq hsz hT d (l + 1) _ (by omega) hw2, hw1]
    · have hpn : ¬ ap trees[l]!.pos (img.toList.getD l 0) < szs.getD l 0 :=
        fun h' => hk ((H.pos_lt _ hx).1 h')
      rw [H.size, decide_eq_false hpn, decide_eq_false hk, Bool.false_and, Bool.false_and]

end CFSG.KC.Co2Eleven.Snd

end
