module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LBase

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {m : G23Model G}

theorem G23LCtx.K1_iso (X : G23LCtx m) :
    Nonempty (↥(frameOf m).K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := X.f1.K1_iso

theorem G23LCtx.K2_iso (X : G23LCtx m) :
    Nonempty (↥(frameOf m).K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := X.f1.K2_iso

theorem G23LCtx.K1_normal (X : G23LCtx m) :
    (frameOf m).K₁ ≤ g23H m ∧ ((frameOf m).K₁.subgroupOf (g23H m)).Normal := X.f1.K1_normal

theorem G23LCtx.K2_normal (X : G23LCtx m) :
    (frameOf m).K₂ ≤ g23H m ∧ ((frameOf m).K₂.subgroupOf (g23H m)).Normal := X.f1.K2_normal

theorem G23LCtx.K_comm (X : G23LCtx m) :
    ∀ u ∈ (frameOf m).K₁, ∀ v ∈ (frameOf m).K₂, u * v = v * u := X.f1.K_comm

theorem G23LCtx.K_inter (X : G23LCtx m) : (frameOf m).K₁ ⊓ (frameOf m).K₂ = (frameOf m).Z :=
  X.f1.K_inter

theorem G23LCtx.pCore1 (X : G23LCtx m) :
    pCoreOf 2 (frameOf m).K₁ = closure {(frameOf m).a₁, (frameOf m).b₁} := X.f1.pCore1

theorem G23LCtx.pCore2 (X : G23LCtx m) :
    pCoreOf 2 (frameOf m).K₂ = closure {(frameOf m).a₂, (frameOf m).b₂} := X.f1.pCore2

theorem G23LCtx.X1_sylow (X : G23LCtx m) : IsSylowIn 3 (frameOf m).K₁ (frameOf m).X₁ :=
  X.f1.X1_sylow

theorem G23LCtx.X2_sylow (X : G23LCtx m) : IsSylowIn 3 (frameOf m).K₂ (frameOf m).X₂ :=
  X.f1.X2_sylow

theorem G23LCtx.h0_inv1 (X : G23LCtx m) :
    ∀ y ∈ (frameOf m).X₁, (frameOf m).h₀ * y * (frameOf m).h₀⁻¹ = y⁻¹ := X.f1.h0_inv1

theorem G23LCtx.h0_inv2 (X : G23LCtx m) :
    ∀ y ∈ (frameOf m).X₂, (frameOf m).h₀ * y * (frameOf m).h₀⁻¹ = y⁻¹ := X.f1.h0_inv2

theorem G23LCtx.sigma_K1 (X : G23LCtx m) :
    conjSub (frameOf m).σ (frameOf m).K₁ = (frameOf m).K₂ := X.f1.sigma_K1

theorem G23LCtx.fact16 (X : G23LCtx m) : (frameOf m).Fact16 m.L := by
  have hc := X.centEl_z
  refine ⟨⟨X.z_mem_invols, m.invol_conj⟩, hc, X.K1_iso, X.K2_iso, ?_, ?_, X.K_comm, X.K_inter,
    X.pCore1, X.pCore2, X.X1_sylow, X.X2_sylow, X.h0_inv1, X.h0_inv2, X.sigma_K1⟩
  · rw [hc]
    exact X.K1_normal
  · rw [hc]
    exact X.K2_normal

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
