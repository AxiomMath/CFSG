module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem up34Core_of_leaves (hAlt : Up34AltLeaf) (hSpor : Up34SporLeaf) (hOdd : Up34OddLeaf)
    (hChev2 : Up34Chev2Leaf) (hD44 : Up34D44Centre) (hL364 : Up34L364NotInnDiag) :
    Up34Core := by
  intro Q _ _ hq hK h3 β hpump
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2
  have hnab : ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hq
  have hpS := Up34Pumpup.descend hq hpump
  obtain ⟨i, ⟨f⟩⟩ := isCatalogGroup_center_quotient_of_isKGroup hK hq
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn => exact (hAlt _ n hn ⟨f⟩ _ hpS).elim
  | lie d =>
    by_cases hd : IsCharTwoLieIndex d.1
    · rcases hChev2 _ hq.2 hnab ⟨d, hd, ⟨f⟩⟩ _ hpS with h | h | h
      · exact Or.inl ⟨h, hL364 Q hq h β hpump⟩
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ⟨?_, hD44 Q hq h⟩)
        obtain ⟨d', hd', ⟨e⟩⟩ := h
        have hZ := hD44 Q hq ⟨d', hd', ⟨e⟩⟩
        exact ⟨d', hd', ⟨(QuotientGroup.quotientBot.symm.trans
          (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e⟩⟩
    · exact (hOdd _ hq.2 hnab d hd ⟨f⟩ _ hpS).elim
  | sporadic name => exact (hSpor _ hq.2 hnab name ⟨f⟩ _ hpS).elim

end CFSG.HardMathSupport.Dickson.Sec6
