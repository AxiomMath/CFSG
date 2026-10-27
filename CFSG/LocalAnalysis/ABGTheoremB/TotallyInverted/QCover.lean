module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] (σ : Setting G)

@[expose] def QCoverFact : Prop :=
  ∀ K : Subgroup G, K ≤ σ.N → σ.C ≤ K → IsQGroup K →
    (σ.L₀ : Set G) ⊆ (K : Set G) * (σ.ON : Set G)

end Setting

end CFSG.ABGTheoremB
