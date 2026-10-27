module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.GH74.KGroups.CoverM11
public import CFSG.GH74.Generic.GKFSporadic
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuCover
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzCover
public import CFSG.Sporadic.Recognition.J4Multiplier
public import CFSG.Sporadic.Recognition.McLMultiplierCert
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import Certificates.Certificate15024
public import Certificates.Certificate15026
public import Certificates.Certificate15030
public import Certificates.Certificate15031
public import Certificates.Certificate15033
public import Certificates.Certificate15034
public import Certificates.Certificate15035
public import Certificates.Certificate15042
public import Certificates.Certificate15043

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

@[expose] def RowBound (s : TauCeti.SporadicName) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → IsPGroup 2 (center L) →
    CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) s →
      Nat.card (center L) ∣ twoPartBound s ∧ (s = .M22 → IsCyclic (center L))

theorem centralTwoBound_of_rows (h : ∀ s, RowBound s) : CentralTwoBound :=
  fun L _ _ hq hZ s hs => h s L hq hZ hs

theorem card_eq_one_of_odd {Z : Type*} [Group Z] (h2 : IsPGroup 2 Z) (hodd : Odd (Nat.card Z)) :
    Nat.card Z = 1 :=
  h2.card_eq_or_dvd.resolve_right fun h => Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 h)

theorem card_dvd_two_of_le_two {Z : Type*} [Group Z] [Finite Z] (h2 : IsPGroup 2 Z)
    (hle : Nat.card Z ≤ 2) : Nat.card Z ∣ 2 := by
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rw [hn] at hle ⊢
  rcases n with _ | _ | n
  · simp
  · simp
  · exfalso
    have : 0 < 2 ^ n := by positivity
    rw [pow_add] at hle
    omega

theorem center_eq_bot_of_noPerfectDoubleCover {X : Type*} [Group X]
    (hX : CFSG.Monster.Schur.NoPerfectDoubleCover X) {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (hZ : IsPGroup 2 (center L)) (e : L ⧸ center L ≃* X) :
    center L = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ (card_eq_one_of_odd hZ
    (CFSG.ComponentClassification.RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover hX L hq.1
      ⟨e⟩))

theorem rowBound_of_center_eq_bot {s : TauCeti.SporadicName} (hb : twoPartBound s = 1)
    (hs : s ≠ .M22)
    (h : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → IsPGroup 2 (center L) →
      CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) s → center L = ⊥) :
    RowBound s :=
  fun L _ _ hq hZ hsp => ⟨by simp [h L hq hZ hsp, hb], fun h' => absurd h' hs⟩

theorem rowBound_of_card_center_le_two {s : TauCeti.SporadicName} (hb : twoPartBound s = 2)
    (hs : s ≠ .M22)
    (h : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → IsPGroup 2 (center L) →
      CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) s → Nat.card (center L) ≤ 2) :
    RowBound s :=
  fun L _ _ hq hZ hsp =>
    ⟨by rw [hb]; exact card_dvd_two_of_le_two hZ (h L hq hZ hsp), fun h' => absurd h' hs⟩

theorem rowBound_M11 :
    RowBound .M11 :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs =>
    CFSG.GH74.KGroups.M11.noTwoCover_M11 (L ⧸ center L) hs L
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff L).2.2.1.2 hq) hZ ⟨MulEquiv.refl _⟩

theorem rowBound_J1 : RowBound .J1 :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs =>
    CFSG.GH74.Generic.noTwoCover_J1_of_walter (L ⧸ center L) hs L
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff L).2.2.1.2 hq) hZ ⟨MulEquiv.refl _⟩

theorem rowBound_M12 :
    RowBound .M12 :=
  rowBound_of_card_center_le_two rfl (by decide) fun L _ _ hq hZ hs =>
    CFSG.ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound L hq hZ
      (Or.inl hs)

theorem rowBound_J2 :
    RowBound .J2 :=
  rowBound_of_card_center_le_two rfl (by decide) fun L _ _ hq hZ hs =>
    CFSG.ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound L hq hZ
      (Or.inr hs)

theorem rowBound_M24 :
    RowBound .M24 :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact center_eq_bot_of_noPerfectDoubleCover
      CFSG.Monster.Schur.noPerfectDoubleCover_nativeM24 hq hZ e

theorem rowBound_J4 :
    RowBound .J4 :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact center_eq_bot_of_noPerfectDoubleCover
      (CFSG.Sporadic.Recognition.J4Multiplier.noPerfectDoubleCover_J4
        Certificates.certificate15042 Certificates.certificate15043) hq hZ e

theorem rowBound_McL :
    RowBound .McL :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact Subgroup.eq_bot_of_card_eq _ (card_eq_one_of_odd hZ (Odd.of_dvd_nat (by decide)
      (CFSG.Sporadic.Recognition.McLMultiplier.card_center_dvd_three_of_certificate
        (Group.isPerfect_def.2 hq.1) e)))

theorem rowBound_He :
    RowBound .He :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq _ hs =>
    CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate L
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff L).2.2.1.2 hq) hs

theorem rowBound_Ru :
    RowBound .Ru :=
  rowBound_of_card_center_le_two rfl (by decide) fun L _ _ hq hZ hs =>
    CFSG.ComponentClassification.RankTwoSporadic.Ru.ruCentralTwoGroupOrderBound_of_checks
      Certificates.certificate15024 Certificates.certificate15026 L hq hZ hs

theorem rowBound_Suz :
    RowBound .Suz :=
  rowBound_of_card_center_le_two rfl (by decide) fun L _ _ hq hZ hs =>
    CFSG.ComponentClassification.RankTwoSporadic.Suz.suzCentralTwoGroupOrderBound_of_checks
      Certificates.certificate15030 Certificates.certificate15031
      Certificates.certificate15033 Certificates.certificate15034
      Certificates.certificate15035 L hq hZ hs

end CFSG.EvenSporadicStandard
