module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.Module
public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def SQTKCharTwoOrAltNative (S : Type) [Group S] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
  StatedClassicalModel S .PSL 2 5 1 ∨ StatedClassicalModel S .PSL 2 7 1 ∨
  StatedClassicalModel S .PSL 2 3 2 ∨ StatedClassicalModel S .PSU 3 3 1 ∨
  ((∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f)) ∨
    ReeTitsModel S .Tits 2 1) ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel S .PSL n 2 1)

@[expose] def AsB42DichotomyNat : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤ →
      CFSG.Milestones.SQTKSimpleList (↥L ⧸ Subgroup.center ↥L) →
      ∀ E : Subgroup (MulAut W), E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ →
        IsElemAbelian2 E → Nat.card W ≤ Nat.card E * Nat.card (fixV E) →
        SQTKCharTwoOrAltNative (↥L ⧸ Subgroup.center ↥L) ∧
          (Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) →
            Subgroup.center ↥L = ⊥)

end CFSG.QuasithinUnique.Bridge
