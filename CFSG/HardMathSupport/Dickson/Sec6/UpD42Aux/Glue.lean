module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Descent
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem upD42Core_of_leaves (hAlt : UpD42AltLeaf) (hSpor : UpD42SporLeaf) (hOdd : UpD42OddLeaf)
    (hChev2 : UpD42Chev2Leaf) : UpD42Core := by
  intro Q _ _ hq hK h3 β hpump
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2
  let : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hsimple
  have hnab : ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hq
  have hpS := UpD42Pumpup.descend hq hpump
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
    · rcases hChev2 _ hq.2 hnab ⟨d, hd, ⟨f⟩⟩ _ hpS with hBig | hTwE6 | hD48
      · exact Or.inl hBig
      · exact Or.inr (Or.inl hTwE6)
      · exact Or.inr (Or.inr hD48)
    · exact (hOdd _ hq.2 hnab d hd ⟨f⟩ _ hpS).elim
  | sporadic name =>
    have hKq : CFSG.Open.IsKGroup (Q ⧸ Subgroup.center Q) :=
      isKGroup_quotient' hK (Subgroup.center Q)
    exact (hSpor _ hq.2 hnab hKq name ⟨f⟩ _ hpS).elim

end CFSG.HardMathSupport.Dickson.Sec6

end
