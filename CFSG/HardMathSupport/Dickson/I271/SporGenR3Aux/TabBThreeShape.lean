module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenBM

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

@[expose] def TabBThreeBNoComp : Prop :=
  ∀ s : NativeSporadic.B, orderOf s = 3 →
    (∀ d : NativeSporadic.B, BabyInv 0 d → d * s * d⁻¹ ≠ s⁻¹) →
      ∀ J : Subgroup NativeSporadic.B,
        ¬ GLAPComponent 3 (Subgroup.centralizer ({s} : Set NativeSporadic.B)) J

section Table


theorem tabBThree_centShapeRk' (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) (hA : TabBThreeACard) (hB : TabBThreeBNoComp) :
    CentShapeRk' 3 (GoodSpor 3 [.Fi22]) (RkSpor 3 [.Fi22]) NativeSporadic.B := by
  intro k hk1 hk3
  have hk : orderOf k = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hk3 hk1
  by_cases hinv : ∃ d : NativeSporadic.B, BabyInv 0 d ∧ d * k * d⁻¹ = k⁻¹
  · obtain ⟨d, hd, hdk⟩ := hinv
    exact tabBThree_shapeRkAt'_of_inverted hOut hSpM hBr hA hk hd hdk
  · exact Or.inl (hB k hk fun d hd h => hinv ⟨d, hd, h⟩)

theorem bThreeShape_of_tab (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) (hA : TabBThreeACard) (hB : TabBThreeBNoComp) : BThreeShape :=
  tabBThree_centShapeRk' hOut hSpM hBr hA hB

theorem sporPair_B_three_of_tab (hOut : SporadicOuterLeTwo)
    (hSpM : SporadicMultipliers) (hBr : SporadicBridges) (hP : SporadicOnePairHolds .B 3)
    (hChev : ChevStrong 3) (hFi22 : SporStrong .Fi22 3) (hA : TabBThreeACard)
    (hB : TabBThreeBNoComp) : SporPair .B 3 :=
  sporPair_B_three_of_shape hOut hSpM hBr hP hChev hFi22 (bThreeShape_of_tab hOut hSpM hBr hA hB)

end Table

end CFSG.HardMathSupport.Dickson.I271
