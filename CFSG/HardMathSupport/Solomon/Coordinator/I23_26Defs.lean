module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26BGL

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

@[expose] def ONGeneration : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    Nonempty ((Y ⧸ Subgroup.center Y) ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) →
    ∀ B : Subgroup Y, IsElemAbelian 3 (B.map (QuotientGroup.mk' (Subgroup.center Y))) →
      Nat.card (B.map (QuotientGroup.mk' (Subgroup.center Y))) = 27 →
        (⊤ : Subgroup Y) ≤ ⨆ (b : Y) (_ : b ∈ B) (_ : b ∉ Subgroup.center Y),
          GLAPLayer 3 (Subgroup.centralizer ({b} : Set Y))

@[expose] def AutL3ElemStructure : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsExtremalType (K ⧸ Subgroup.center K) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → Nat.card E = 27 →
      (∃ b ∈ E, IsFieldAutThree b ∧ b ≠ 1) ∧ ∃ x ∈ E, IsInnDiagThree x ∧ x ≠ 1

@[expose] def AutL3NoE27OffType : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsLThreeEpsBar (K ⧸ Subgroup.center K) → ¬ IsExtremalType (K ⧸ Subgroup.center K) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → Nat.card E ≠ 27

end CFSG.HardMathSupport.Solomon.Coordinator
