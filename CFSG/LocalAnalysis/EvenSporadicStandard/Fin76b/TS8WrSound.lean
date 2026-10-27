module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Table
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrModel

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8Wr

open CFSG.EvenSporadicStandard.Fin76b

@[expose] def TabR {G : Type*} [Group G] (ζ α t g₁ g₂ h₁ h₂ : G) : Prop :=
  ζ * ζ = 1 ∧ α * α = 1 ∧ t * t = 1 ∧ α ≠ 1 ∧ t ≠ 1 ∧ α ≠ t ∧ α * t = t * α ∧
    ζ * t = t * ζ ∧ ζ * α = α * t * ζ ∧ h₁ * ζ = ζ * g₁ ∧ h₂ * ζ = ζ * g₂ ∧
    (g₁ * α = α * g₁ ∧ g₁ * t = t * g₁) ∧ (g₂ * α = α * g₂ ∧ g₂ * t = t * g₂) ∧
    (h₁ * α = α * h₁ ∧ h₁ * t = t * h₁) ∧ (h₂ * α = α * h₂ ∧ h₂ * t = t * h₂) ∧
    (g₁ * g₁ = 1 ∨ g₁ * g₁ = t) ∧ (g₂ * g₂ = 1 ∨ g₂ * g₂ = t) ∧
    g₁ * g₂ = α * t * (g₂ * g₁) ∧ h₁ * h₂ = α * (h₂ * h₁) ∧
    g₁ * h₂ = t * (h₂ * g₁) ∧ g₂ * h₁ = t * (h₁ * g₂) ∧ g₁ * h₁ = h₁ * g₁ ∧ g₂ * h₂ = h₂ * g₂

@[expose] def NoTabSig : Prop :=
  ∀ ζ α t g₁ g₂ h₁ h₂ : Pt, ζ ∈ Sig → α ∈ Sig → t ∈ Sig → g₁ ∈ Sig → g₂ ∈ Sig →
    h₁ ∈ Sig → h₂ ∈ Sig → TabR ζ α t g₁ g₂ h₁ h₂ → False

theorem tabR_of_outerTable {X : Type*} [Group X] {ζ α t g₁ g₂ h₁ h₂ : X}
    (h : OuterTable ζ α t g₁ g₂ h₁ h₂) : TabR ζ α t g₁ g₂ h₁ h₂ := by
  obtain ⟨hζζ, hαα, htt, hα1, ht1, hαt, hαtc, hζα', hζt', hh1', hh2', _, hcs, hsq1, hsq2,
    hgg', hhh', hgh', hhg', hg1h1, hg2h2⟩ := h
  refine ⟨hζζ, hαα, htt, hα1, ht1, hαt, hαtc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hsq1, hsq2, ?_, ?_, ?_, ?_, hg1h1, hg2h2⟩
  · calc ζ * t = ζ * t * ζ⁻¹ * ζ := by group
      _ = t * ζ := by rw [hζt']
  · calc ζ * α = ζ * α * ζ⁻¹ * ζ := by group
      _ = α * t * ζ := by rw [hζα']
  · rw [hh1']
    group
  · rw [hh2']
    group
  · exact hcs g₁ (by simp)
  · exact hcs g₂ (by simp)
  · exact hcs h₁ (by simp)
  · exact hcs h₂ (by simp)
  · calc g₁ * g₂ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ * (g₂ * g₁) := by group
      _ = α * t * (g₂ * g₁) := by rw [hgg']
  · calc h₁ * h₂ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ * (h₂ * h₁) := by group
      _ = α * (h₂ * h₁) := by rw [hhh']
  · calc g₁ * h₂ = g₁ * h₂ * g₁⁻¹ * h₂⁻¹ * (h₂ * g₁) := by group
      _ = t * (h₂ * g₁) := by rw [hgh']
  · calc g₂ * h₁ = g₂ * h₁ * g₂⁻¹ * h₁⁻¹ * (h₁ * g₂) := by group
      _ = t * (h₁ * g₂) := by rw [hhg']

end CFSG.EvenSporadicStandard.Fin76b.TS8Wr
