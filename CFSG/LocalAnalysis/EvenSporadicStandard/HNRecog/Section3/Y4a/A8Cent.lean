module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_card_Gx_two_two {s : alternatingGroup (Fin 8)}
    (hs : (s : Equiv.Perm (Fin 8)).cycleType = {2, 2}) : Nat.card ↥(Gx s) = 96 := by
  classical
  have hclass : Nat.card {c : alternatingGroup (Fin 8) // IsConj s c} =
      (Finset.univ.filter (fun g : alternatingGroup (Fin 8) =>
        (g : Equiv.Perm (Fin 8)).cycleType = {2, 2})).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply congrArg Finset.card
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hc
      have hc' : IsConj (s : Equiv.Perm (Fin 8)) (c : Equiv.Perm (Fin 8)) :=
        (alternatingGroup (Fin 8)).subtype.map_isConj hc
      rw [Equiv.Perm.isConj_iff_cycleType_eq] at hc'
      rw [hs] at hc'
      exact hc'.symm
    · intro hc
      exact isConj_of_cycleType_two_two hs hc
  have hcount : (Finset.univ.filter (fun g : alternatingGroup (Fin 8) =>
        (g : Equiv.Perm (Fin 8)).cycleType = {2, 2})).card = 210 := by
    have h := AlternatingGroup.card_of_cycleType (Fin 8) ({2, 2} : Multiset ℕ)
    simp only [Fintype.card_fin] at h
    norm_num [Nat.factorial] at h
    exact h
  have hG : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h := card_isConj_mul_card_centralizer (G := alternatingGroup (Fin 8)) s
  rw [hclass, hcount, hG] at h
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
