module

public import CFSG.GF2Type.Smith1979.CaseIClosure
public import CFSG.GF2Type.Smith1979.CaseIChain
public import CFSG.GF2Type.Smith1979.CaseICount
public import CFSG.GF2Type.Smith1979.SixCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem caseITwoCentral (hCE : CentralExtInput.{0}) (hnoAll : S11.NoA2All S) {g : G}
    (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h6 : finrank (ZMod 2) (Vt S g t) = 6) (hN : Nbar S g t = zpowers t)
    (h2c : TwoCentralBar S t) :
    ∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
      (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
        Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)) := by
  have hNo : NoA2 S g := noA2_of (hnoAll g H.conj_mem H.conj_ne)
  have hSC := strongClosed_six hCE countSixStmt H hNo C ht ht1 hVQ hΩ hN h6 h2c
  obtain ⟨q, hq, hiso⟩ :=
    timmesfeld_7_7_of_omegaCase_sc hCE H hNo C ht ht1 hVQ hΩ hN h6.ge hSC
  obtain ⟨q', hnd', -, ⟨eΩ⟩, ⟨eO⟩⟩ := Bridge.exists_fin_form q h6
  refine ⟨q', hnd' ((Bridge.polarBilin_nondegenerate_iff q).mp hq), ?_⟩
  rcases hiso with hA | hB
  · obtain ⟨f⟩ := hA
    exact Or.inl ⟨f.trans (MulEquiv.prodCongr (MulEquiv.refl _) eΩ)⟩
  · obtain ⟨f⟩ := hB
    exact Or.inr ⟨f.trans (MulEquiv.prodCongr (MulEquiv.refl _) eO)⟩

@[expose] def CaseINotTwoCentralStmt : Prop :=
  Smith1980Orth.TimInputs → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ S : Setting G, S.width = 6 →
      ¬ S.IsReducible → S11.NoA2All S → ∀ {g : G} (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
        (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
        OmegaCase H C ht ht1 hVQ → finrank (ZMod 2) (Vt S g t) = 6 → Nbar S g t = zpowers t →
          ¬ TwoCentralBar S t → TwoFi22.ParrottShape S.M ∧ ¬ IsCharTwoType G

theorem caseIStmt_of_notTwoCentral (hCE : CentralExtInput.{0}) (h25 : CaseINotTwoCentralStmt) :
    CaseIStmt := by
  intro I G _ _ _ hK S hw hirr hnoAll g H C t ht ht1 hVQ hΩ h6 hN
  by_cases h2c : TwoCentralBar S t
  · exact Or.inl (caseITwoCentral hCE hnoAll H C ht ht1 hVQ hΩ h6 hN h2c)
  · exact Or.inr (h25 I G hK S hw hirr hnoAll H C ht ht1 hVQ hΩ h6 hN h2c)

end CFSG.GF2Type.Smith1979
