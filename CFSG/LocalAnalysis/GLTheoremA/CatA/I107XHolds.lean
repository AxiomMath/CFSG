module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107XTabs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107EG2Quot
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.GH74.Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107XPRank
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Symplectic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107E

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.I107X (simplyLaced_pRank_ge)


theorem twoRankLow_E6_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .E6) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .E6 := ht
  have hn : 1 ≤ n := hlab.1
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨-, hna, ⟨θ⟩⟩ := hQ
  have e0 : LargeEvenCenterQuot (LargeEvenChevH (CFSG.Assembly.LargeEvenCartanE 6) K false) ≃*
      AdjointQuotient Tag.E6 K :=
    (CFSG.StandardType.centerQuot_chevGroup_equiv K Tag.E6).some
  haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH (CFSG.Assembly.LargeEvenCartanE 6) K false)) :=
    Finite.of_equiv _ θ.toEquiv
  haveI : Finite (AdjointQuotient Tag.E6 K) := Finite.of_equiv _ e0.toEquiv
  rw [CFSG.LocalAnalysis.GLTheoremA.I107L.pRank_eq_of_quotient θ hna,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e0]
  have hcount := CFSG.LocalAnalysis.GLTheoremA.I107X.simplyLaced_pRank_ge (Or.inl rfl) (K := K) (n := n)
    hn hK (List.ofFn CFSG.LocalAnalysis.GLTheoremA.I107X.psiE6)
    CFSG.LocalAnalysis.GLTheoremA.I107X.psiE6_ok CFSG.LocalAnalysis.GLTheoremA.I107X.psiE6_nodup
    CFSG.LocalAnalysis.GLTheoremA.I107X.psiE6_chain
  rw [List.length_ofFn] at hcount
  exact hcount

theorem twoRankLow_E7_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .E7) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .E7 := ht
  have hn : 1 ≤ n := hlab.1
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨-, hna, ⟨θ⟩⟩ := hQ
  have e0 : LargeEvenCenterQuot (LargeEvenChevH (CFSG.Assembly.LargeEvenCartanE 7) K false) ≃*
      AdjointQuotient Tag.E7 K :=
    (CFSG.StandardType.centerQuot_chevGroup_equiv K Tag.E7).some
  haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH (CFSG.Assembly.LargeEvenCartanE 7) K false)) :=
    Finite.of_equiv _ θ.toEquiv
  haveI : Finite (AdjointQuotient Tag.E7 K) := Finite.of_equiv _ e0.toEquiv
  rw [CFSG.LocalAnalysis.GLTheoremA.I107L.pRank_eq_of_quotient θ hna,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e0]
  have hcount := CFSG.LocalAnalysis.GLTheoremA.I107X.simplyLaced_pRank_ge (Or.inr (Or.inl rfl)) (K := K) (n := n)
    hn hK (List.ofFn CFSG.LocalAnalysis.GLTheoremA.I107X.psiE7)
    CFSG.LocalAnalysis.GLTheoremA.I107X.psiE7_ok CFSG.LocalAnalysis.GLTheoremA.I107X.psiE7_nodup
    CFSG.LocalAnalysis.GLTheoremA.I107X.psiE7_chain
  rw [List.length_ofFn] at hcount
  exact hcount

theorem twoRankLow_E8_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .E8) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .E8 := ht
  have hn : 1 ≤ n := hlab.1
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨-, hna, ⟨θ⟩⟩ := hQ
  have e0 : LargeEvenCenterQuot (LargeEvenChevH (CFSG.Assembly.LargeEvenCartanE 8) K false) ≃*
      AdjointQuotient Tag.E8 K :=
    (CFSG.StandardType.centerQuot_chevGroup_equiv K Tag.E8).some
  haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH (CFSG.Assembly.LargeEvenCartanE 8) K false)) :=
    Finite.of_equiv _ θ.toEquiv
  haveI : Finite (AdjointQuotient Tag.E8 K) := Finite.of_equiv _ e0.toEquiv
  rw [CFSG.LocalAnalysis.GLTheoremA.I107L.pRank_eq_of_quotient θ hna,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e0]
  have hcount := CFSG.LocalAnalysis.GLTheoremA.I107X.simplyLaced_pRank_ge (Or.inr (Or.inr rfl)) (K := K) (n := n)
    hn hK (List.ofFn CFSG.LocalAnalysis.GLTheoremA.I107X.psiE8)
    CFSG.LocalAnalysis.GLTheoremA.I107X.psiE8_ok CFSG.LocalAnalysis.GLTheoremA.I107X.psiE8_nodup
    CFSG.LocalAnalysis.GLTheoremA.I107X.psiE8_chain
  rw [List.length_ofFn] at hcount
  exact hcount

end CFSG.LocalAnalysis.GLTheoremA.I107E

end
