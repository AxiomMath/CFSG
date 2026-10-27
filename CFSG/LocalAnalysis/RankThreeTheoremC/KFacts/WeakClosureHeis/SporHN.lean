module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporDispatch
public import CFSG.RankThree.PartOne.Q1327S.HN

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Blueprint CFSG.RankThree.PartOne.KS.HNFive CFSG.RankThree.PartOne.Q1327S

theorem sdSpor_HN5 :
    SDSporAt .HN 5 := by
  intro K _ _ ⟨e⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨q, z, x, r, hR⟩ := exists_hn_rel
  haveI hfin : Finite (NativeSporadic.Carrier .HN) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card NativeSporadic.HN ≠ 0
      rw [CFSG.Sporadic.HN.card_HN]; norm_num)
  refine SylowDichotomyAt.of_mulEquiv Nat.prime_five e ?_
  have hcardQ : Nat.card (QG q) = 5 ^ 5 := hR.card_Q
  exact SylowDichotomyAt.of_exponent (U := QG q) (IsPGroup.of_card hcardQ)
    (fun u hu => hR.pow_five_of_mem hu) hcardQ.symm.le

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
