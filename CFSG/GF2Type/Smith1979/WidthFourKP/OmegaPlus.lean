module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Faithful
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.OddCore
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.ThreeFour
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Triple
public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Final
public import CFSG.GF2Type.Smith1979.W4FiveTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G]

@[expose] def WidthFourOmegaPlusLayerFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ S : Setting G, S.width = 4 → S11.NoA2All S → ¬ S.IsReducible →
    ∀ g : G, ∀ (H : Hyp4 S g) (C : Cons311 S g), ¬ Nonempty (S5.SwapData S g) →
      ∀ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      OmegaCase H C ht ht1 hVQ → finrank (ZMod 2) (Vt S g t) = 4 → PlusTypeAt S g ht →
      CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) →
      (∀ l ∈ S.Lbar g, (∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype, l * y = y * l) →
        l = 1) →
      False

namespace OmegaPlus

variable {S : Setting G} {g : G}

theorem of_layer_eq_bot (hw : S.width = 4) (hnoAll : S11.NoA2All S) (hirr : ¬ S.IsReducible)
    (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht)
    (hE : timmesfeldLayer S.Mbar = ⊥) :
    (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
        (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
          Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
      (∃ E : Subgroup S.O, E ≤ S.Mbar ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) ∨
      TrialityConfig S g t := by
  have hNo : NoA2 S g := fun α h1 h2 h3 => hnoAll g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  rcases card_oddCore_of_layer_eq_bot hw H hNo C hE with h27 | ⟨h81, p, hp, hp1, hfix⟩
  · rcases of_card_oddCore_eq_twentyseven hw hnoAll hirr H C ht ht1 hVQ hΩ h4 hplus hE h27 with
      h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · refine Or.inr (Or.inl ⟨S7.Obar S, S7.Obar_le_Mbar, isElemAbelian_Obar H hNo C hp hfix, ?_⟩)
    rw [S7.card_Obar, h81]

end OmegaPlus

theorem widthFourOmegaPlus_of_layer
    (hQ2 : WidthFourOmegaPlusLayerFalse) : WidthFourOmegaPlus := by
  intro G _ _ _ hnab hchar hK S hw hno hirr g H C t ht ht1 hVQ hΩ h4 hplus
  have hCE : CentralExtInput.{0} := S4.centralExtInput
  have hsw : ¬ Nonempty (S5.SwapData S g) :=
    widthFourSwapFalse_of_centralExtInput hCE G hnab hchar hK S hw hno hirr g H C
  have hNo : NoA2 S g := fun α h1 h2 h3 => hno g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  rcases W4Five.timmesfeld_5_2_w4 hCE (S14.irr_of_not_isReducible hirr) H hNo C
      (S45Q.hyp45Q H C) hw with hE | hq | hs
  · exact OmegaPlus.of_layer_eq_bot hw hno hirr H C ht ht1 hVQ hΩ h4 hplus hE
  · exact (hQ2 G hnab hchar hK S hw hno hirr g H C hsw t ht ht1 hVQ hΩ h4 hplus hq
      (OmegaPlus.layer_faithful hCE hw hno hirr H C ht ht1 hVQ hΩ h4 hplus hq)).elim
  · exact (hsw hs).elim

end CFSG.GF2Type.Smith1979

end
