module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.MainNative
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2W
public import CFSG.GH74.Uniqueness.Section165GapFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverMain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspNotRankLie
public import CFSG.LocalAnalysis.Asc75.EndFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native39
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedClosed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeEmbedding256
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeProp121
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4Excl
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Asc75Proof
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Bend
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinList
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Final
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinCoverMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinNonIso
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Final
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Cat
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Main
public import CFSG.Quasithin.Background.KnownMultTypes

public section

namespace CFSG.QuasithinUnique

theorem unconstrainedBranch_of_open_inputs
    (hJ4 : Ch1.J4OutOdd) (h246 : Lemma246Inputs)
    (hpairs : Vol2Native.L239.L239ParabolicPairs) (h2519 : Lemma2519) : UnconstrainedBranch :=
  have h36 := Vol2Native.a36CoreForSQTKCat_proved
  have h37 := Vol2Native.a37ForSQTKCat_proved
  have h38 := Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact
    Vol2Native.a134SQTKFactCat h36 h37
  have hS := Ch1.sporadicRestAutInner_of_J4OutOdd hJ4
  have hschL := Vol2Native.schreierFactListCat_of_J4 (sporadicSchreierCase_J4_of_outOdd hJ4)
  have h39 := Vol2Native.a39ForSQTKCat_of_facts hschL h36 h37 h38
  have hlist := lemma115_3_List_of_rest_inputs' K1.titsSylowCentralizingAutInner hS
    Ch1.titsTwoCoverTrivial
  have hMB : MinParabolicBlocks :=
    Setup.Top.minParabolicBlocks_final (Setup.X1.sporadicExclusion_J4_of_outerOdd hJ4)
  have h2397 := Vol2Native.lemma2_3_9_7W_of_open_inputs' h37 h38
    (L238.lemma2_3_8_4_of_inputs hMB h37 h246) hlist Vol2Native.L239.l239NotRankOne hpairs
    Vol2Native.L239.l239M22Parabolic Vol2Native.L239.l239M23Parabolic
  have h252 : Lemma252 := lemma252_of_rankTwoW h2397 rankTwoBorelFacts
  unconstrainedBranch_of_remaining_parts h252
    (Fin253.lemma253Component_of_borel_list h252 (Fin253.lemma253Bender h252) hschL
        rankTwoBorelFacts)
    (Vol2Native.lemma256Embedding_of_a3 h37 h39) a312Sublist
    (lemma257_of_inputs
        ⟨rankTwoBorelFacts, Fin257.nonIso257, (Vol2Native.prop121Three_of_a3 h37 h38),
            Fin257.geom257, Fin257.maxRank257, Fin257.cover257a, Fin257.torus257, Fin257.autOdd257⟩)
    lemma258_proved k33LocalFacts l33AutFacts a6OuterTypes h2519
    (lemma2521_of_asc (asc75Lemma34Disjoint_of_endgame
        (CFSG.Asc75.asc75Endgame_of_ZD CFSG.GH74.Uniqueness.S_ZD_unconditional)))
    lemma2522 lemma2524 lemma2525 (lemma2526 lemma2526Claim) lemma2527
    (lemma25Final lemma25FinalBadCaseExcluded)

end CFSG.QuasithinUnique
