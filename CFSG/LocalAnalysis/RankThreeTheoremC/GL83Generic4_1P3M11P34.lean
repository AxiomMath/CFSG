module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem GL83GenericPrimeThreeM11Prop34.of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact) :
    GL83GenericPrimeThreeM11Prop34 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  exact m11_prop34 hS hU0 hD1 hKM hKA hKT hSig hp hM hgen
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩

theorem genericPrimeThree_of_types4_of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact) (hno : NoExcludedSection3 G)
    (h4 : GL83GenericPrimeThreeTypes4 G) (h42 : GL83GenericPrimeThreeM11Lemma42 G)
    (h43 : GL83GenericPrimeThreeM11Lemma43 G) : GL83GenericPrimeThree G :=
  genericPrimeThree_of_types4 hS hU0 hD1 K1 K2 K3 K4 hInn hWC hKM hKA hno h4
    (.of_kfacts hS hU0 hD1 hKM hKA hKT hSig) h42 h43

end CFSG.LocalAnalysis.RankThreeTheoremC
