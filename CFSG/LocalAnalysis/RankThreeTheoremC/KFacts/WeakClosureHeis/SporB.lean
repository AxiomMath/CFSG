module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporDispatch
public import CFSG.RankThree.Native.BFiveLocalRel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Blueprint CFSG.Monster.B.Pinned CFSG.RankThree.Native

theorem sdSpor_B5 :
    SDSporAt .B 5 := by
  intro K _ _ ⟨e⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hfin : Finite (NativeSporadic.Carrier .B) := finite_B
  refine SylowDichotomyAt.of_mulEquiv Nat.prime_five e ?_
  have hR := bFiveRel
  have hcardQ : Nat.card (FiveLocal.Q qFive) = 5 ^ 5 := hR.card_Q
  exact SylowDichotomyAt.of_exponent (U := FiveLocal.Q qFive) (IsPGroup.of_card hcardQ)
    (fun u hu => hR.pow_five_of_mem hu) hcardQ.symm.le

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
