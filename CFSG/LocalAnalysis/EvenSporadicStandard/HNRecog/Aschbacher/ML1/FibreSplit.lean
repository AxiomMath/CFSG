module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.Transfer

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

theorem exists_mulEquiv_of_fibre {L L' : Type} [Group L] [Group L'] [Finite L] [Finite L']
    (F : Subgroup (L × L')) (z : L) (z' : L')
    (hz : (z, (1 : L')) ∈ F) (hz' : ((1 : L), z') ∈ F)
    (hπ₁ : ∀ l : L, ∃ l' : L', (l, l') ∈ F) (hπ₂ : ∀ l' : L', ∃ l : L, (l, l') ∈ F)
    (hk₁ : ∀ l' : L', ((1 : L), l') ∈ F → l' = 1 ∨ l' = z')
    (hk₂ : ∀ l : L, (l, (1 : L')) ∈ F → l = 1 ∨ l = z)
    (Δ : Subgroup F) [Δ.Normal] (hzc : (⟨(z, 1), hz⟩ : F) ∈ Subgroup.center F)
    (hzΔ : (⟨(z, 1), hz⟩ : F) ∉ Δ)
    (hzz' : ∃ h : (z, z') ∈ F, (⟨(z, z'), h⟩ : F) ∈ Δ)
    (T : Subgroup F) (hΔT : Δ ≤ T) (hzT : (⟨(z, 1), hz⟩ : F) ∈ T) (hT : Odd T.index)
    (hsq : ∀ t ∈ T, t ^ 2 ∈ Δ) :
    ∃ e : L ≃* L', ∀ l : L, (l, e l) ∈ F := by
  classical
  haveI : Finite ↥F :=
    Finite.of_injective (fun x : ↥F => (x : L × L')) Subtype.coe_injective
  obtain ⟨lam, hlam_z, hlam_Δ⟩ :=
    exists_hom_C2_of_odd_index Δ ⟨(z, 1), hz⟩ hzc hzΔ T hΔT hzT hT hsq
  obtain ⟨hzz, hzzΔ⟩ := hzz'
  have hsplit : (⟨(z, z'), hzz⟩ : F) = ⟨(z, 1), hz⟩ * ⟨(1, z'), hz'⟩ := by
    apply Subtype.ext
    simp
  have hprod : lam ⟨(z, 1), hz⟩ * lam ⟨(1, z'), hz'⟩ = 1 := by
    rw [← map_mul, ← hsplit]
    exact hlam_Δ _ hzzΔ
  have hlam_z' : lam ⟨(1, z'), hz'⟩ ≠ 1 := by
    intro h1
    exact hlam_z (by simpa [h1] using hprod)
  exact exists_mulEquiv_of_hom_C2 F z z' hz hz' hπ₁ hπ₂ hk₁ hk₂ lam hlam_z hlam_z'

end CFSG.EvenSporadicStandard.HNRecog.ML1
