module

public import CFSG.GH74.GLS.Balance.Bender.Ambient
public import CFSG.GH74.GLS.Balance.Bender.Stmts

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem l56_le_mul_centralizer {p : ℕ} [Fact p.Prime] (h55 : BenderL55 p) {G : Type} [Group G] [Finite G]
    {X Z M P N : Subgroup G} (hZX : Z ≤ X) (hMZ : M ≤ Z) (hMn : (M.subgroupOf Z).Normal)
    (hPM : P ≤ M) (hPp : IsPGroup p ↥P) (hNZ : N ≤ Z) (hNX : N ≤ X) (hNn : (N.subgroupOf X).Normal)
    (hNp : IsPStar p ↥N) : N ≤ M ⊔ (Z ⊓ centralizer (P : Set G)) := by
  have hPnorm : P ≤ normalizer (N : Set G) := fun x hx =>
    (Subgroup.le_normalizer_of_normal_subgroupOf hNX) (hZX (hMZ (hPM hx)))
  have h := h55 G N P hNp hPp hPnorm
  have hcomm : ⁅N, P⁆ ≤ M := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    have h1 : g₁ * g₂ * g₁⁻¹ ∈ M := hMn.conj_mem ⟨g₂, hMZ (hPM hg₂)⟩ (hPM hg₂) ⟨g₁, hNZ hg₁⟩
    have h2 : ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := commutatorElement_def g₁ g₂
    rw [h2]
    exact mul_mem h1 (inv_mem (hPM hg₂))
  have hcent : oResOf p (N ⊓ centralizer (P : Set G)) ≤ Z ⊓ centralizer (P : Set G) :=
    (oResOf_le p _).trans (inf_le_inf_right _ hNZ)
  calc N = ⁅N, P⁆ ⊔ oResOf p (N ⊓ centralizer (P : Set G)) := h
    _ ≤ M ⊔ (Z ⊓ centralizer (P : Set G)) := sup_le_sup hcomm hcent

theorem bender_l56 {p : ℕ} [Fact p.Prime] (h55 : BenderL55 p) : BenderL56 p := by
  intro G _ _ X N₁ N₂ h1X h2X hn1 hn2 hp1 hp2
  have hZX : N₁ ⊔ N₂ ≤ X := sup_le h1X h2X
  rw [isPStar_iff]
  refine ⟨?_, fun M P hMZ hMn hP => ?_⟩
  · refine le_antisymm (oResOf_le p _) (sup_le ?_ ?_)
    · calc N₁ = oResOf p N₁ := hp1.oResOf_eq.symm
        _ ≤ oResOf p (N₁ ⊔ N₂) := oResOf_mono le_sup_left
    · calc N₂ = oResOf p N₂ := hp2.oResOf_eq.symm
        _ ≤ oResOf p (N₁ ⊔ N₂) := oResOf_mono le_sup_right
  · obtain ⟨hPM, hPp, -⟩ := hP
    exact sup_le
      (l56_le_mul_centralizer h55 hZX hMZ hMn hPM hPp le_sup_left h1X hn1 hp1)
      (l56_le_mul_centralizer h55 hZX hMZ hMn hPM hPp le_sup_right h2X hn2 hp2)

end CFSG.GH74.GLS.Balance
