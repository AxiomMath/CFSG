module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallJ4
public import CFSG.GH74.KGroups.M11Tables
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Sporadic.Recognition.McLASInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem not_dvd_of_card_dvd_two {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : n ∣ 2) : ¬ p ∣ n :=
  fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hd.trans h))

theorem autPInner_of_isM11
    {p : ℕ} {K : Type} [Group K] [Finite K] (hK : IsSporadicGroup .M11 K) : AutPInner p K := by
  obtain ⟨e⟩ := nonempty_equiv_m11 hK
  rintro f -
  obtain ⟨k, hk⟩ := CFSG.GH74.KGroups.M11.out_trivial ⟨e⟩ f
  exact ⟨k, MulEquiv.ext fun x => (hk x).symm⟩

theorem autPInner_of_isTitsGroup
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hK : IsTitsGroup K) : AutPInner p K := by
  obtain ⟨e⟩ := nonempty_equiv_tits hK
  exact autPInner_of_equiv hp e
    (not_dvd_of_card_dvd_two hp hp2 (by rw [CFSG.Sporadic.Schreier.Tits.card_outer_titsD]))

theorem autPInner_of_isMcL
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hK : IsSporadicGroup .McL K) : AutPInner p K := by
  obtain ⟨e⟩ := nonempty_equiv_mclP hs hK
  have h2 : Nat.card (Outer NativeSporadic.McL) = 2 :=
    CFSG.Sporadic.Recognition.McLAS.card_outer_mcl
  have h3 : ¬ p ∣ Nat.card (Outer NativeSporadic.McL) := by
    rw [h2]
    exact not_dvd_of_card_dvd_two hp hp2 (dvd_refl 2)
  have e' : K ≃* NativeSporadic.McL := e.trans CFSG.Sporadic.Schreier.mclPermEquiv.symm
  exact @autPInner_of_equiv K _ p NativeSporadic.McL inferInstance hp e' h3

theorem autPInner_of_isFi22
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hK : IsFi22 K) : AutPInner p K := by
  obtain ⟨e⟩ := nonempty_equiv_fi22 hs hK
  have h2 : Nat.card (Outer NativeSporadic.Fi22) = 2 :=
    CFSG.ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22
  have h3 : ¬ p ∣ Nat.card (Outer NativeSporadic.Fi22) := by
    rw [h2]
    exact not_dvd_of_card_dvd_two hp hp2 (dvd_refl 2)
  exact @autPInner_of_equiv K _ p NativeSporadic.Fi22 inferInstance hp e h3

theorem autPInner_of_isJ4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hK : IsSporadicGroup .J4 K) : AutPInner p K := by
  obtain ⟨e⟩ := nonempty_equiv_j4 hs hK
  have h1 : Nat.card (Outer (NativeSporadic.Carrier .J4)) = 1 :=
    CFSG.AGLEmbedding.card_outer_J4
  have h3 : ¬ p ∣ Nat.card (Outer (NativeSporadic.Carrier .J4)) := by
    rw [h1]
    exact not_dvd_of_card_dvd_two hp hp2 (one_dvd 2)
  have e' : K ≃* NativeSporadic.Carrier .J4 :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat).symm
  exact @autPInner_of_equiv K _ p (NativeSporadic.Carrier .J4) inferInstance hp e' h3

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
