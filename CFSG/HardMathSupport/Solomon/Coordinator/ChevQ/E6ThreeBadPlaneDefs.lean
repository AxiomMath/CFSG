module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadCube

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar


@[expose] def E6PlaneCosetStmt : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (ω : Kˣ), ω ^ 3 = 1 → ω ≠ 1 →
    ∀ u ∈ toralCentralizer .E6 K (e6LineChar ω), u ∉ toralRootGroup .E6 K (e6LineChar ω) →
      Module.finrank K ↥(LinearMap.ker ((u : Module.End K (RootModule .E6 K)) - 1) ⊓
        LinearMap.ker ((rootDiagUnit .E6 (e6LineChar ω) : Module.End K (RootModule .E6 K)) - 1))
          ≤ 8

@[expose] def E6PlaneToralStmt : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (ω : Kˣ), ω ^ 3 = 1 → ω ≠ 1 →
    ∀ u ∈ toralRootGroup .E6 K (e6LineChar ω), u ^ 3 = 1 →
      Module.finrank K ↥(LinearMap.ker ((u : Module.End K (RootModule .E6 K)) - 1) ⊓
        LinearMap.ker ((rootDiagUnit .E6 (e6LineChar ω) : Module.End K (RootModule .E6 K)) - 1))
          = 12 →
      ∃ y ∈ toralRootGroup .E6 K (e6LineChar ω), ∃ b : Fin Tag.E6.rank → Kˣ,
        (∀ i, b i ^ 3 = 1) ∧ y * u * y⁻¹ = rootDiagUnit .E6 b

@[expose] def E6PlaneWeylStmt : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (ω : Kˣ), ω ^ 3 = 1 → ω ≠ 1 →
    ∀ b : Fin Tag.E6.rank → Kˣ, (∀ i, b i ^ 3 = 1) →
      (∀ k : ℕ, k < 3 → Module.finrank K (LinearMap.ker
        ((((rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) ^ k * rootDiagUnit .E6 b :
          ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 30) →
      ∃ g ∈ adjointGroup .E6 K,
        g⁻¹ * rootDiagUnit .E6 (e6LineChar ω) * g ∈
          Subgroup.zpowers (rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) ⊔
            Subgroup.zpowers (rootDiagUnit .E6 b : ModGL .E6 K) ∧
        g⁻¹ * rootDiagUnit .E6 (e6D0Char ω) * g ∈
          Subgroup.zpowers (rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) ⊔
            Subgroup.zpowers (rootDiagUnit .E6 b : ModGL .E6 K)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
