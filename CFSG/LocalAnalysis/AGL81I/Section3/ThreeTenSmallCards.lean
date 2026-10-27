module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenThreeCard
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoSL

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem natCard_alternatingGroup_fin_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [natCard_alternatingGroup_fin 7 (by norm_num)]
  norm_num

theorem natCard_alternatingGroup_fin_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [natCard_alternatingGroup_fin 6 (by norm_num)]
  norm_num

theorem natCard_alternatingGroup_fin_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [natCard_alternatingGroup_fin 5 (by norm_num)]
  norm_num

theorem natCard_eq_card_subgroup_mul_card_quotient {X : Type} [Group X]
    (N : Subgroup X) [N.Normal] :
    Nat.card X = Nat.card N * Nat.card (X ⧸ N) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, mul_comm]

theorem natCard_of_isExtNotation {PA PB : ∀ (V : Type) [Group V], Prop} {X : Type} [Group X]
    (h : IsExtNotation PA PB X) :
    ∃ (N : Subgroup X) (_ : N.Normal), PB ↥N ∧ PA (X ⧸ N) ∧
      Nat.card X = Nat.card N * Nat.card (X ⧸ N) := by
  obtain ⟨N, hN, hBN, hAN, -⟩ := h
  haveI := hN
  exact ⟨N, hN, hBN, hAN, natCard_eq_card_subgroup_mul_card_quotient N⟩

theorem natCard_of_isExtNotation_alternating_seven_two {X : Type} [Group X]
    (h : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 7)))
      (fun B _ => Nat.card B = 2) X) :
    Nat.card X = 5040 := by
  obtain ⟨N, hN, hBN, hAN, hcard⟩ := natCard_of_isExtNotation h
  haveI := hN
  obtain ⟨e⟩ := hAN
  have hquot : Nat.card (X ⧸ N) = 2520 := by
    rw [Nat.card_congr e.toEquiv, natCard_alternatingGroup_fin_seven]
  rw [hcard, hquot, hBN]

theorem natCard_of_isExtNotation_alternating_six_two {X : Type} [Group X]
    (h : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
      (fun B _ => Nat.card B = 2) X) :
    Nat.card X = 720 := by
  obtain ⟨N, hN, hBN, hAN, hcard⟩ := natCard_of_isExtNotation h
  haveI := hN
  obtain ⟨e⟩ := hAN
  have hquot : Nat.card (X ⧸ N) = 360 := by
    rw [Nat.card_congr e.toEquiv, natCard_alternatingGroup_fin_six]
  rw [hcard, hquot, hBN]

theorem natCard_of_isExtNotation_zmod_five_q8d8 {X : Type} [Group X]
    (h : IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) X) :
    Nat.card X = 5 * 32 := by
  obtain ⟨N, hN, hBN, hAN, hcard⟩ := natCard_of_isExtNotation h
  rw [hcard, hAN, natCard_of_isQ8D8Type hBN]

end CFSG.LocalAnalysis.AGL81I.Section3
