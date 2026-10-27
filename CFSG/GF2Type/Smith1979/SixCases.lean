module

public import CFSG.GF2Type.Smith1979.SixStage
public import CFSG.GF2Type.Smith1979.WidthSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.GF2Type.Smith1980Orth CFSG.EvenSporadicStandard

@[expose] def CaseIStmt : Prop :=
  TimInputs → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ S : Setting G, S.width = 6 →
      ¬ S.IsReducible → S11.NoA2All S → ∀ {g : G} (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
        (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
        OmegaCase H C ht ht1 hVQ → finrank (ZMod 2) (Vt S g t) = 6 → Nbar S g t = zpowers t →
          (∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
            (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
              Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
          (TwoFi22.ParrottShape S.M ∧ ¬ IsCharTwoType G)

@[expose] def CaseIIStmt : Prop :=
  TimInputs → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ S : Setting G, S.width = 6 →
      ¬ S.IsReducible → S11.NoA2All S → ∀ {g : G} (H : Hyp4 S g) (C : Cons311 S g),
        (∀ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
          ¬ (OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = 6 ∧
            Nbar S g t = zpowers t)) →
        ∀ {t : S.O} (ht : t ∈ S.Lbar g), t ≠ 1 → LinCase S g ht →
          finrank (ZMod 2) (Vt S g t) = 3 →
            Quasithin.H13.J4.IsTypeJ4Core S.M (Quasithin.H13.J4.selfC S.z) ∧
              Quasithin.H13.J4.IsAutTripleM22 (S.M ⧸ CFSG.pCore 2 S.M)

@[expose] def CaseIIIStmt : Prop :=
  TimInputs → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ S : Setting G, S.width = 6 →
      ¬ S.IsReducible → S11.NoA2All S → ∀ {g : G} (H : Hyp4 S g) (C : Cons311 S g),
        (∀ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
          ¬ (OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = 6 ∧
            Nbar S g t = zpowers t)) →
        (∀ (t : S.O) (ht : t ∈ S.Lbar g), t ≠ 1 →
          ¬ (LinCase S g ht ∧ finrank (ZMod 2) (Vt S g t) = 3)) → False

theorem widthSixCore_of_cases (I : TimInputs) (h1 : CaseIStmt) (h2 : CaseIIStmt)
    (h3 : CaseIIIStmt) : WidthSixCore := by
  intro G _ _ _ hK S hw hex hirr
  obtain ⟨hnoAll, g, -, -, H, C, -⟩ := sixStage I hw hex hirr
  by_cases hI : ∃ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = 6 ∧ Nbar S g t = zpowers t
  · obtain ⟨t, ht, ht1, hVQ, hΩ, h6, hN⟩ := hI
    rcases h1 I G hK S hw hirr hnoAll H C ht ht1 hVQ hΩ h6 hN with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  push Not at hI
  by_cases hII : ∃ (t : S.O) (ht : t ∈ S.Lbar g), t ≠ 1 ∧ LinCase S g ht ∧
      finrank (ZMod 2) (Vt S g t) = 3
  · obtain ⟨t, ht, ht1, hL, h3'⟩ := hII
    exact Or.inr (Or.inr (h2 I G hK S hw hirr hnoAll H C (fun t ht ht1 hVQ h =>
      hI t ht ht1 hVQ h.1 h.2.1 h.2.2) ht ht1 hL h3'))
  · push Not at hII
    exact (h3 I G hK S hw hirr hnoAll H C (fun t ht ht1 hVQ h => hI t ht ht1 hVQ h.1 h.2.1 h.2.2)
      (fun t ht ht1 h => hII t ht ht1 h.1 h.2)).elim

end CFSG.GF2Type.Smith1979
