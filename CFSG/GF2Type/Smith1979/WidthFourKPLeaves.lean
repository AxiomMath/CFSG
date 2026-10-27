module

public import CFSG.LargeExtraspecial.S4TwoF
public import CFSG.LargeExtraspecial.S11Basic
public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.Yardstones.M3aba7dc4b8a8

@[expose] def WidthFourTrialityCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ S : Setting G, S.width = 4 → S11.NoA2All S → ¬ S.IsReducible →
    ∀ g : G, ∀ (H : Hyp4 S g) (C : Cons311 S g),
      StatedClassicalModel (M0 S g) .PSL 2 2 3 → LieModel G .trialityD4 0 2 1

@[expose] def ParrottThKP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2 (coreQ z) → Nat.card (coreQ z) = 2 ^ 9 → ¬ ZWeaklyClosedInCore z →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        Nonempty (Mbar ≃* alternatingGroup (Fin 9)) → IsSporadic G .Th

@[expose] def WidthFourOmegaCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ S : Setting G, S.width = 4 → S11.NoA2All S → ¬ S.IsReducible →
    ∀ g : G, ∀ (H : Hyp4 S g) (C : Cons311 S g) (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
      (hVQ : ¬ V S g t ≤ S.Qa g), OmegaCase H C ht ht1 hVQ → Module.finrank (ZMod 2) (Vt S g t) = 4 →
      (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
          (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
            Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
        IsSporadic G .HN ∨
        ∃ E : Subgroup S.O, E ≤ S.Mbar ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4

end CFSG.GF2Type.Smith1979
