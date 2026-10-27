module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Jordan.HeisRepADefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6HeisDescent

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis (repA repD)


theorem heisClass_dichotomy {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) {w : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizer a)
    (hsh : rootChar a (e6Shift w) ≠ 1) : HeisClassA a w ∨ HeisClassD a w := by
  obtain ⟨b, hker, hwb, hshb⟩ := exists_triData a ha3 hw hsh
  obtain ⟨t, b', hb', hpair, hwt, hsht⟩ := exists_rep b hwb hshb
  rcases hb' with rfl | rfl
  · exact Or.inr ⟨b, t, hker, hpair, hwt, hsht⟩
  · exact Or.inl ⟨b, t, hker, hpair, hwt, hsht⟩

theorem e6HeisFrameFixedElt_of_classes (hA : E6HeisFrameFixedEltA) (hD : E6HeisFrameFixedEltD) :
    E6HeisFrameFixedElt := by
  intro K _ _ hK3 hK4 E hEab hcard hd F
  rcases heisClass_dichotomy F.a F.ha3 F.hw F.hsh with h | h
  · exact hA K hK3 hK4 E hEab hcard hd F h
  · exact hD K hK3 hK4 E hEab hcard hd F h

theorem twE6HeisFrameFixedElt_of_classes (hA : TwE6HeisFrameFixedEltA)
    (hD : TwE6HeisFrameFixedEltD) : TwE6HeisFrameFixedElt := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ E hE hEab hcard F
  rcases heisClass_dichotomy F.a F.ha3 F.hw F.hsh with h | h
  · exact hA ℓ f hℓ hℓ3 hf K hK σ hσ E hE hEab hcard F h
  · exact hD ℓ f hℓ hℓ3 hf K hK σ hσ E hE hEab hcard F h

end CFSG.LieType.SeitzGeneration.ExcWideThree
