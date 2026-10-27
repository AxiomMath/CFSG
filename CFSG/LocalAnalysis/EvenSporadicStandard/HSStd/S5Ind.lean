module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.BasicSec
public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulSolomon
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
open CFSG.EvenSporadicStandard.Induction
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

@[expose] def HSMainA8 : GroupPred := fun H _ _ =>
  CFSG.oddCore H = ⊥ →
    ∀ A : Subgroup H, standardComponentIsStandard A →
      Nonempty (↥A ≃* alternatingGroup (Fin 8)) →
      Open.pRank 2 (centralizer (A : Set H)) = 1 →
      (∀ t : H, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set H)) = ⊥) →
        SolomonAltOutcome H A 8

@[expose] def HSMainHiS : GroupPred := fun H _ _ =>
  CFSG.oddCore H = ⊥ →
    ∀ A : Subgroup H, standardComponentIsStandard A → IsSporadic ↥A .HS →
      Open.pRank 2 (centralizer (A : Set H)) = 1 →
      (∀ t : H, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set H)) = ⊥) →
        ∃ K₁ K₂ : Subgroup H, K₁.IsSubnormal ∧ K₂.IsSubnormal ∧
          IsSporadic (K₁ ⧸ center K₁) .HS ∧ IsSporadic (K₂ ⧸ center K₂) .HS ∧
          A ≤ K₁ ⊔ K₂ ∧ (K₁ ⊔ K₂).Normal

@[expose] def HSInductionA8 (G : Type) [Group G] [Finite G] : Prop := BelowSec HSMainA8 G

@[expose] def HSMainHiSKP : GroupPred := fun H _ _ =>
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → HSMainHiS H

@[expose] def HSInductionHiS (G : Type) [Group G] [Finite G] : Prop := BelowSec HSMainHiSKP G

theorem HSInductionHiS.uHered {G : Type} [Group G] [Finite G] (h : HSInductionHiS G) :
    Balance.UHered G :=
  BelowSec.uHered h

end CFSG.EvenSporadicStandard.HSStd
