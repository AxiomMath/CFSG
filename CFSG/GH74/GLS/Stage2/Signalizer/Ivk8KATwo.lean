module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KATwoA
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KATwoD
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KATwoE
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184Graph
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP2Interface
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux
public import CFSG.GH74.GLS.IVK.Lifted.IIAutB
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.GH74.GLS.IVK.Lifted.Strong
public import CFSG.GH74.GLS.Stage1.Main.Basic
public import CFSG.GH74.GLS.Stage1.Main.BrFusedBase
public import CFSG.GH74.GLS.Stage1.Main.BrFusedPair
public import CFSG.GH74.GLS.Stage1.Main.BrG2Base
public import CFSG.GH74.GLS.Stage1.Main.BrIndex
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassA
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassI
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassU
public import CFSG.GH74.GLS.Stage1.Main.II4Proof
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47c
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafC1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx64
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic25
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Axb
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der62
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs9
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt12
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
public import CFSG.GH74.GLS.Stage2.Signalizer.Kinds
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Arith
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.SDWr
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.Generic.S3.B2Tab1
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.Sporadic.Th.Max3.Packet

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kay_L34 :
    KAY (fun (Y : Type) [Group Y] => LieModel Y .PSL 3 2 2) := by
  intro Y _ _ hF _ α hα2 hα1 p hp hp2 P hP hP1 hcomm hnorm
  obtain ⟨hi, h⟩ := ka34_of_model hF hα2 hα1 hp hp2 hP hP1 hcomm hnorm
  refine ⟨hi, ?_⟩
  rcases h with hc | ⟨hp3, hinn, hcard⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hF, hp3, unitaryFix_of_card_seventytwo hF hα2 hinn hcard⟩

theorem kay_Two :
    KAY FTwo := by
  intro Y _ _ hF hs α hα2 hα1 p hp hp2 P hP hP1 hcomm hnorm
  rcases hF with h28 | h216 | h34 | hu34 | hsz
  · exact kay_TwoBender Y (Or.inl h28) hs α hα2 hα1 p hp hp2 P hP hP1 hcomm hnorm
  · exact kay_TwoBender Y (Or.inr (Or.inl h216)) hs α hα2 hα1 p hp hp2 P hP hP1 hcomm hnorm
  · exact kay_L34 Y h34 hs α hα2 hα1 p hp hp2 P hP hP1 hcomm hnorm
  · exact kay_TwoBender Y (Or.inr (Or.inr (Or.inl hu34))) hs α hα2 hα1 p hp hp2 P hP hP1 hcomm
      hnorm
  · exact kay_TwoBender Y (Or.inr (Or.inr (Or.inr hsz))) hs α hα2 hα1 p hp hp2 P hP hP1 hcomm
      hnorm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
