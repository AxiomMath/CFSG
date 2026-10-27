module

public import CFSG.GroupTheory.QuasiDihedralFusion.Defs
public import CFSG.LocalAnalysis.ABGTheoremB.Basic

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec10

open CFSG.QuasiDihedralFusion

@[expose] def QGroupFourFusion (G : Type) [Group G] : Prop :=
  ∀ H : Subgroup G, IsQGroup H → ∀ T₁ : Subgroup G, T₁ ≤ H → IsKleinFour T₁ →
    ∃ z ∈ T₁, z ≠ 1 ∧ (∀ h ∈ H, h * z * h⁻¹ * z⁻¹ ∈ oddCoreIn H) ∧
      ∀ t ∈ T₁, t ≠ 1 → t ≠ z → ∃ h ∈ H, h * t * h⁻¹ = t * z

@[expose] def DGroupFourFusion (G : Type) [Group G] : Prop :=
  (∃ n : ℕ, HasSemidihedralSylow G n) → ∀ H : Subgroup G, IsDGroup H →
    ∀ T₁ : Subgroup G, T₁ ≤ H → IsKleinFour T₁ → ∀ t ∈ T₁, t ≠ 1 →
      (∃ h ∈ H, ∃ t' ∈ T₁, t' ≠ t ∧ h * t * h⁻¹ = t') ∨
        ∃ T₂ : Subgroup G, T₂ ≤ H ∧ IsKleinFour T₂ ∧ t ∈ T₂ ∧
          3 ∣ automizerIndex (T₂.subgroupOf H)

end CFSG.ABGTheoremB.TotallyInverted.Sec10
