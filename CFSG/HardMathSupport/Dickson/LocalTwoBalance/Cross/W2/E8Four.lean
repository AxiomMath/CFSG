module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Setup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveSmall
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ3
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterT

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge


theorem e8InnerFiveFour_holds : E8InnerFiveFour := by
  intro q hv _ h5
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at h5
  have hAK := anyKindCommute_of_T anyKindCommuteT_holds
  have hrig : SetupRigidAtFrobenius .E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1 ∧ 3 ≤ q := by
    intro K _ _ Fr hFr g0 hg0C hg0 S hSD hQ
    by_cases hq4 : 4 ≤ Nat.card K
    · exact setupRigidAtFrobenius_E8_of_anyKind (by norm_num) bigAnyPBigAtFrobenius_E8_four_five
        hAK K Fr hFr g0 hg0C hg0 S hSD ⟨hQ.1, hq4⟩
    · have : Nat.card K = 3 := by omega
      exact setupRigidAtFrobenius_E8_four_five_three anyKindCommuteThreeFull_holds K Fr hFr g0
        hg0C hg0 S hSD this
  exact InnerPlaneBalance.of_mulEquiv e
    (W2.innerPlaneBalance_adjointE8_four_five K h5 t1_pieces hAK anyKindCommuteThreeFull_holds
      (fun δ _ => e8PhiFourWeyl_sq_smul δ) hrig)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
