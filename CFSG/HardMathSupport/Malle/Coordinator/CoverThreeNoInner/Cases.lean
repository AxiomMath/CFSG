module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (psuConj)

section Action

variable {Y : Type*} [Group Y]

@[expose] noncomputable def modelAct (K : Subgroup Y) [K.Normal] {M : Type*} [Group M]
    (e : K ⧸ Subgroup.center K ≃* M) : Y →* MulAut M :=
  (MulAut.congr e).toMonoidHom.comp
    ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K).comp
      MulAut.conjNormal)

end Action

@[expose] def CoverThreeNoInnerDiagLinear : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rb : Sylow 3 Y) (Y₀ : Subgroup Y),
    ReducedNongeneration 3 Y Rb Y₀ →
    ∀ (K : Subgroup Y) [K.Normal], Open.IsQuasisimple K →
      Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
        c ∈ (Subgroup.center K).map K.subtype) →
      (Nat.card (Subgroup.center K)).factorization 3 = 1 →
      ∀ (F : Type) [Field F] [Finite F], 3 ∣ Nat.card F - 1 →
      ∀ e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F,
      ∀ E : Subgroup Y, E ≤ (Rb : Subgroup Y) → E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore →
        IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y) →
        E.map (modelAct K e) ≤ linearAutGroup 3 F → False

@[expose] def CoverThreeNoInnerFieldLinear : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rb : Sylow 3 Y) (Y₀ : Subgroup Y),
    ReducedNongeneration 3 Y Rb Y₀ →
    ∀ (K : Subgroup Y) [K.Normal], Open.IsQuasisimple K →
      Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
        c ∈ (Subgroup.center K).map K.subtype) →
      (Nat.card (Subgroup.center K)).factorization 3 = 1 →
      ∀ (F : Type) [Field F] [Finite F], 3 ∣ Nat.card F - 1 →
      ∀ e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F,
      ∀ E : Subgroup Y, E ≤ (Rb : Subgroup Y) → E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore →
        IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y) →
        ¬ E.map (modelAct K e) ≤ linearAutGroup 3 F → False

@[expose] def CoverThreeNoInnerDiagUnitary : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rb : Sylow 3 Y) (Y₀ : Subgroup Y),
    ReducedNongeneration 3 Y Rb Y₀ →
    ∀ (K : Subgroup Y) [K.Normal], Open.IsQuasisimple K →
      Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
        c ∈ (Subgroup.center K).map K.subtype) →
      (Nat.card (Subgroup.center K)).factorization 3 = 1 →
      ∀ (ℓ f : ℕ) (F : Type) [Field F] (h : UnitaryFieldData ℓ f F), 2 < ℓ ^ f →
        3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 8 →
      ∀ e : K ⧸ Subgroup.center K ≃* unitaryPSU h 3,
      ∀ E : Subgroup Y, E ≤ (Rb : Subgroup Y) → E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore →
        IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y) →
        E.map (modelAct K e) ≤ (psuConj h).range → False

@[expose] def CoverThreeNoInnerFieldUnitary : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rb : Sylow 3 Y) (Y₀ : Subgroup Y),
    ReducedNongeneration 3 Y Rb Y₀ →
    ∀ (K : Subgroup Y) [K.Normal], Open.IsQuasisimple K →
      Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
        c ∈ (Subgroup.center K).map K.subtype) →
      (Nat.card (Subgroup.center K)).factorization 3 = 1 →
      ∀ (ℓ f : ℕ) (F : Type) [Field F] (h : UnitaryFieldData ℓ f F), 2 < ℓ ^ f →
        3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 8 →
      ∀ e : K ⧸ Subgroup.center K ≃* unitaryPSU h 3,
      ∀ E : Subgroup Y, E ≤ (Rb : Subgroup Y) → E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore →
        IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y) →
        ¬ E.map (modelAct K e) ≤ (psuConj h).range → False

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
