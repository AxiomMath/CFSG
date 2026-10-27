module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGRed
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spor

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup Assembly.LowTwoRank SporRow

theorem false_of_perfect3 {S : Type} [Group S] [Finite S] {t : S}
    (hO : pPrimeCore 2 ↥(centralizer ({t} : Set S)) = ⊥) {J : Subgroup S}
    (hJC : J ≤ centralizer {t}) (hJs : (J.subgroupOf (centralizer {t})).IsSubnormal)
    (htJ : t ∈ J) (hJq : IsTwoQuasisimple ↥J) {L : Type} [Group L]
    (hind : IndLieOrder (Nat.card (L ⧸ Open.fusionZStar L)))
    (eL : L ⧸ Open.fusionZStar L ≃* ↥J ⧸ Open.fusionZStar ↥J)
    (hcomp : ∀ B : Subgroup ↥(centralizer ({t} : Set S)), IsComponent B → selfCent t ∈ B →
      ¬ IndLieOrder (Nat.card (↥B ⧸ center ↥B))) : False := by
  set C := centralizer ({t} : Set S)
  set B := J.subgroupOf C
  let eB : ↥B ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
  have hOB : pPrimeCore 2 ↥B = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hJs
  have hOJ : pPrimeCore 2 ↥J = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eB, hOB, Subgroup.map_bot]
  have hBq : IsTwoQuasisimple ↥B := isTwoQuasisimple_of_mulEquiv eB.symm hJq
  have hBq' : IsQuasisimple ↥B := LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hOB).trans QuotientGroup.quotientBot) hBq.2
  have hB : IsComponent B := ⟨hBq', hJs⟩
  have htB : selfCent t ∈ B := mem_subgroupOf.2 htJ
  have hcJ : Nat.card (↥J ⧸ Open.fusionZStar ↥J) = Nat.card (↥B ⧸ center ↥B) := by
    rw [card_quotient_fusionZStar_of_bot hOJ]
    exact (Nat.card_congr (QuotientGroup.congr _ _ eB (Subgroup.map_center_eq eB)).toEquiv).symm
  have hL : Nat.card (L ⧸ Open.fusionZStar L) = Nat.card (↥B ⧸ center ↥B) := by
    rw [Nat.card_congr eL.toEquiv, hcJ]
  rw [hL] at hind
  exact hcomp B hB htB hind

section LieOrder


theorem indLieOrder_of_perfType3 {L : Type} [Group L] (h : PerfType3 L) :
    IndLieOrder (Nat.card (L ⧸ Open.fusionZStar L)) := by
  rcases h with hI | ⟨τ, n, hm⟩
  · exact indLieOrder_of_field Nat.prime_three (by norm_num) hI
  · exact indLieOrder_of_lieModel Nat.prime_three (by norm_num) hm
      (.inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))))

end LieOrder

section Certified


theorem rowCore3_spor :
    RowCore3 (fun S => Blueprint.NativeSporadic.SporadicRep S ∧
      ¬ Nonempty (S ≃* ↥Blueprint.NativeSporadic.M11)) := by
  intro S _ _ _ hna ⟨⟨s, ⟨e⟩⟩, hM11⟩ t ht J hJC hJs htJ hJq L _ _ hT ⟨eL⟩
  have hs : s ≠ .M11 := by
    rintro rfl
    exact hM11 ⟨e⟩
  have hd := sporT1Data_of s hs
  exact false_of_perfect3 (hd.oddCore S hna e t ht) hJC hJs htJ hJq
    (indLieOrder_of_perfType3 hT) eL (hd.comps S hna e t ht)

end Certified

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
