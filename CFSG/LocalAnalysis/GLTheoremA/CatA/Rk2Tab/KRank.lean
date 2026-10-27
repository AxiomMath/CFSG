module

public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ClassicalModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE6Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Derived
public import CFSG.CGT.PushingUpLit.CGT6.SixFour
public import CFSG.CGT.PushingUpLit.CGT6.SixSixteen
public import CFSG.CGT.PushingUpLit.Glue.ClassXBasic
public import CFSG.CGT.PushingUpLit.Glue.RadicalSylow
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
public import CFSG.RankThree.PartOne.F106.FiveRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Blueprint.Multiplier CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed CFSG.LieType.Simplicity
  CFSG.LieType.Steinberg.TwistedE6
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial


theorem rk2KRank : Rk2KRank := by
  intro K _ _ lab p hK hp hp2
  have hG : CFSG.Open.GriessAllModelsStatement :=
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  rcases lab with ⟨t, l, n⟩
  cases t
  · exact rk2KRank_classical hG hK hp hp2 (by simp)
  · exact rk2KRank_classical hG hK hp hp2 (by simp)
  · exact rk2KRank_classical hG hK hp hp2 (by simp)
  · exact rk2KRank_classical hG hK hp hp2 (by simp)
  · exact rk2KRank_classical hG hK hp hp2 (by simp)
  · exact rk2KRank_classical hG hK hp hp2 (by simp)
  · exact rk2_pRank_le_E6_all K ⟨.E6, l, n⟩ p hK (by simp) hp hp2
  · exact rk2_pRank_le_E7 (lab := ⟨.E7, l, n⟩) (p := p) hK (by simp) hp hp2
  · exact rk2_pRank_le_E8 K ⟨.E8, l, n⟩ hK (by simp) p hp hp2
  · exact rk2_pRank_le_F4 K ⟨.F4, l, n⟩ p hK (by simp) hp hp2
  · exact rk2_pRank_le_E6_all K ⟨.twE6, l, n⟩ p hK (by simp) hp hp2
  · exact rk2_pRank_le_small hK (by simp) hp hp2
  · exact rk2KRank_G2 hG hK hp hp2 (by simp)
  · exact rk2_pRank_le_small hK (by simp) hp hp2
  · exact rk2_pRank_le_small hK (by simp) hp hp2
  · exact rk2_pRank_le_derived ⟨.B2der, l, n⟩ p hK (by simp) hp hp2
  · exact rk2_pRank_le_derived ⟨.G2der, l, n⟩ p hK (by simp) hp hp2
  · exact rk2_pRank_le_derived ⟨.twF4der, l, n⟩ p hK (by simp) hp hp2

end CFSG.LocalAnalysis.GLTheoremA

end
