module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporDispatch
public import CFSG.RankThree.Native.LyFiveSpec

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Blueprint CFSG.RankThree.Native

theorem sylowDichotomyAt_lyJ_five :
    SylowDichotomyAt CFSG.Sporadic.Ly.J 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ := lyFiveMRelJ.q
  have hcardQ : Nat.card (fiveQ lyFiveXJ lyFiveVJ) = 5 ^ 5 := hQ.card_fiveQ
  exact SylowDichotomyAt.of_exponent (U := fiveQ lyFiveXJ lyFiveVJ) (IsPGroup.of_card hcardQ)
    (fun u hu => hQ.pow_five_of_mem hu) hcardQ.symm.le

theorem sdSpor_Ly5 :
    SDSporAt .Ly 5 := by
  intro K _ _ ⟨e⟩
  have e' : K ≃* NativeSporadic.Ly := e
  have φ : K ≃* CFSG.Sporadic.Ly.J := e'.trans CFSG.Sporadic.Ly.lyEquivJ
  exact @SylowDichotomyAt.of_mulEquiv K _ _ 5 CFSG.Sporadic.Ly.J (inferInstance) (inferInstance)
    Nat.prime_five φ sylowDichotomyAt_lyJ_five

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
