module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
import CFSG.ClassicalInvolution.SmallCases.Hat2A7E5Order

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

theorem lieModel_odd_card_ne_2520 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 2520 :=
  CFSG.ClassicalInvolution.Hat2A7E5.lieModel_odd_card_ne_A7 hO hp2 hadm hX

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem not_oddLieCentralQuotient_alt7 (hO : LieOrderFormulasInput) {p : ℕ} (hp2 : p ≠ 2)
    {L : Type} [Group L] (h : OddLieCentralQuotient p L)
    (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨τ, n, f, hadm, hm⟩ := h
  refine lieModel_odd_card_ne_2520 hO hp2 hadm hm ?_
  rw [Nat.card_congr e.toEquiv]
  exact card_alternatingGroup_seven

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
