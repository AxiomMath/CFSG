module

public import CFSG.GF2Type.Smith1979.WidthFourKPLeaves
public import CFSG.LargeExtraspecial.S5Swap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.Yardstones.M3aba7dc4b8a8 Module

variable {G : Type*} [Group G] [Finite G]

@[expose] def PlusTypeAt (S : Setting G) (g : G) {t : S.O} (ht : t ∈ S.Lbar g) : Prop :=
  ∃ P : Submodule (ZMod 2) (Vt S g t), finrank (ZMod 2) P = 2 ∧
    ∀ v ∈ P, v ≠ 0 → v ∈ orbitOf (RmodN S g t) (aV ht)

@[expose] def PlusAt {S : Setting G} {g : G} (H : Hyp4 S g) (C : Cons311 S g) : Prop :=
  ∃ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
    OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = 4 ∧ PlusTypeAt S g ht

@[expose] def TrialityConfig (S : Setting G) (g : G) (t : S.O) : Prop :=
  timmesfeldLayer S.Mbar = ⊥ ∧ Nat.card (timmesfeldOddCore S.Mbar) = 3 ^ 3 ∧
    ∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ≠ t

@[expose] def WidthFourSwapFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ S : Setting G, S.width = 4 → S11.NoA2All S → ¬ S.IsReducible →
    ∀ g : G, Hyp4 S g → Cons311 S g → ¬ Nonempty (S5.SwapData S g)

@[expose] def WidthFourOmegaMinus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ S : Setting G, S.width = 4 → S11.NoA2All S → ¬ S.IsReducible →
    ∀ g : G, ∀ (H : Hyp4 S g) (C : Cons311 S g) (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
      (hVQ : ¬ V S g t ≤ S.Qa g), OmegaCase H C ht ht1 hVQ → finrank (ZMod 2) (Vt S g t) = 4 →
      ¬ PlusAt H C →
      ∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
        (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
          Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))

@[expose] def WidthFourOmegaPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ S : Setting G, S.width = 4 → S11.NoA2All S → ¬ S.IsReducible →
    ∀ g : G, ∀ (H : Hyp4 S g) (C : Cons311 S g) (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
      (hVQ : ¬ V S g t ≤ S.Qa g), OmegaCase H C ht ht1 hVQ → finrank (ZMod 2) (Vt S g t) = 4 →
      PlusTypeAt S g ht →
      (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
          (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
            Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
        (∃ E : Subgroup S.O, E ≤ S.Mbar ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) ∨
        TrialityConfig S g t

@[expose] def WidthFourOmegaTrialityFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ S : Setting G, S.width = 4 → S11.NoA2All S → ¬ S.IsReducible →
    ∀ g : G, ∀ (H : Hyp4 S g) (C : Cons311 S g) (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
      (hVQ : ¬ V S g t ≤ S.Qa g), OmegaCase H C ht ht1 hVQ → finrank (ZMod 2) (Vt S g t) = 4 →
      PlusTypeAt S g ht →
      (¬ ∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
          (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
            Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) →
      ¬ TrialityConfig S g t

theorem widthFourOmegaCase_of_cases (hm : WidthFourOmegaMinus) (hp : WidthFourOmegaPlus)
    (htr : WidthFourOmegaTrialityFalse) : WidthFourOmegaCase := by
  intro G _ _ _ hnab hchar hK S hw hno hirr g H C t ht ht1 hVQ hΩ h4
  by_cases hP : PlusAt H C
  · obtain ⟨t', ht', ht1', hVQ', hΩ', h4', hplus⟩ := hP
    rcases hp G hnab hchar hK S hw hno hirr g H C t' ht' ht1' hVQ' hΩ' h4' hplus with
      h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · by_cases hiso : ∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
          (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
            Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))
      · exact Or.inl hiso
      · exact (htr G hnab hchar hK S hw hno hirr g H C t' ht' ht1' hVQ' hΩ' h4' hplus hiso h).elim
  · exact Or.inl (hm G hnab hchar hK S hw hno hirr g H C t ht ht1 hVQ hΩ h4 hP)

end CFSG.GF2Type.Smith1979
