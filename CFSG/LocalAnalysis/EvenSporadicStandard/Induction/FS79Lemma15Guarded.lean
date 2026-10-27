module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.SignalizerFunctorTheorem (IsSectionOf)

@[expose] def FS79Lemma15Hered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → FS79Lemma15At H

@[expose] def FS79Lemma15Sec (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSectionOf X G → FS79Lemma15At X

theorem FS79Lemma15Hered.sec (h : FS79Lemma15Hered) {G : Type} [Group G] [Finite G]
    (hG : Balance.UHered G) : FS79Lemma15Sec G :=
  fun X _ _ hX => h X (hG.of_section hX)

theorem FS79Lemma15Sec.at {G : Type} [Group G] [Finite G] (h : FS79Lemma15Sec G) :
    FS79Lemma15At G :=
  h G (IsSectionOf.refl G)

end CFSG.EvenSporadicStandard.Induction
