module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagAssembly

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree

section Elt

variable {K : Type} [Field K]

@[expose] def e6LineElt (ω : Kˣ) : adjointGroup Tag.E6 K :=
  ⟨rootDiagUnit .E6 (e6LineChar ω),
    (mem_toralCentralizer.1 (torusGroup_le_toralCentralizer (e6LineChar ω)
      (e6Line_diag_mem_torusGroup ω))).1⟩

@[simp] theorem coe_e6LineElt (ω : Kˣ) :
    (e6LineElt ω : ModGL .E6 K) = rootDiagUnit .E6 (e6LineChar ω) :=
  rfl

end Elt

@[expose] def E6ThreeA2ConjStmt : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (ω : Kˣ), ω ^ 3 = 1 → ω ≠ 1 →
    ∀ x ∈ adjointGroup .E6 K, x ^ 3 = 1 →
      Module.finrank K (LinearMap.ker ((x : Module.End K (RootModule .E6 K)) - 1)) = 24 →
      ∃ g ∈ adjointGroup .E6 K, g * x * g⁻¹ = rootDiagUnit .E6 (e6LineChar ω)

@[expose] def E6ThreeA2WitnessStmt : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (ω : Kˣ), ω ^ 3 = 1 → ω ≠ 1 →
    Module.finrank K (LinearMap.ker
      (((rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1))
        = 24

@[expose] def E6InnerAll24
    (K : Type) [Field K] (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) : Prop :=
  ∀ s : adjointGroup Tag.E6 K, MulAut.conj s ∈ E → s ≠ 1 →
    Module.finrank K (LinearMap.ker
      (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24

@[expose] def E6ThreeLayerGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ ω : Kˣ, ω ^ 3 = 1 → ω ≠ 1 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → MulAut.conj (e6LineElt ω) ∈ E →
      ∀ i : Fin 3, (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K) ≤ seitzHyperGamma 3 E

@[expose] def E6ThreeTorusGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ ω : Kˣ, ω ^ 3 = 1 → ω ≠ 1 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
      ¬ E6NormalizesR K E → MulAut.conj (e6LineElt ω) ∈ E →
      torusGroup .E6 K ≤ (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
        rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)))

@[expose] def E6ThreeCompGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ ω : Kˣ, ω ^ 3 = 1 → ω ≠ 1 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
      ¬ E6NormalizesR K E → E6InnerAll24 K E → MulAut.conj (e6LineElt ω) ∈ E →
      canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
        (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
          toralRootGroup .E6 K (e6LineChar ω)

@[expose] def E6ThreeNotAll24Gen :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
      ¬ E6NormalizesR K E → ¬ E6InnerAll24 K E → seitzHyperGamma 3 E = ⊤

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
