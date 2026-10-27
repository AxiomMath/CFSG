module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem GL83GenericPrimeThreeM11.of_parts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (h34 : GL83GenericPrimeThreeM11Prop34 G) (h42 : GL83GenericPrimeThreeM11Lemma42 G)
    (h43 : GL83GenericPrimeThreeM11Lemma43 G) : GL83GenericPrimeThreeM11 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  have h1 := h34 p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  have h2 := h42 p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h1
  have h3 := h43 p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h1
  subst hp3
  exact m11_false_of_plane hS hU0 hD1 hInn hWC hKM hKA hp rfl hM hgen
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩ ⟨h1, h2, h3⟩

theorem GL83GenericPrimeThreeTypes.of_four (h4 : GL83GenericPrimeThreeTypes4 G)
    (hM : GL83GenericPrimeThreeM11 G) : GL83GenericPrimeThreeTypes G :=
  GenericRedThreeAt.mono (fun _ _ hQ => by
    rcases hQ with hQ | hQ | hQ | hQ | hQ
    · exact Or.inl (Or.inl hQ)
    · exact Or.inl (Or.inr (Or.inl hQ))
    · exact Or.inr hQ
    · exact Or.inl (Or.inr (Or.inr (Or.inl hQ)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr hQ)))) (h4.union hM)

theorem GL83GenericPrimeThreeTypes.of_four_parts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (h4 : GL83GenericPrimeThreeTypes4 G) (h34 : GL83GenericPrimeThreeM11Prop34 G)
    (h42 : GL83GenericPrimeThreeM11Lemma42 G) (h43 : GL83GenericPrimeThreeM11Lemma43 G) :
    GL83GenericPrimeThreeTypes G :=
  .of_four h4 (GL83GenericPrimeThreeM11.of_parts hS hU0 hD1 hInn hWC hKM hKA h34 h42 h43)

theorem genericPrimeThree_of_types4 (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hno : NoExcludedSection3 G)
    (h4 : GL83GenericPrimeThreeTypes4 G) (h34 : GL83GenericPrimeThreeM11Prop34 G)
    (h42 : GL83GenericPrimeThreeM11Lemma42 G) (h43 : GL83GenericPrimeThreeM11Lemma43 G) :
    GL83GenericPrimeThree G :=
  genericPrimeThree_of_types hS hU0 K1 K2 K3 K4 hno
    (.of_four_parts hS hU0 hD1 hInn hWC hKM hKA h4 h34 h42 h43)

end CFSG.LocalAnalysis.RankThreeTheoremC
