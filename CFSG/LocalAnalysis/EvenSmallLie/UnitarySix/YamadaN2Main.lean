module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Back
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Gamma

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped MatrixGroups

section Main

variable {G : Type} [Group G] {t : G} {D₁ V₁ D₂ A₂ K₂ : Subgroup G} {θ₂ : SL3 →* G}
  {ιG : (Fin 9 → ZMod 2) → G}

theorem Y14Hyp.normal_nTwo (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    (D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer D₂_le_nTwo).mpr h.nTwo_le_normalizer

theorem Y14Hyp.centralizer_of_fix [Fact (ElemSec D₂ (⊥ : Subgroup G))]
    [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG)
    (hfix : ∀ γ, tauG2 h γ = γ → γ ∈ (theta2 h).range)
    {x : G} (hx : x ∈ nTwo D₂ K₂ D₁) (hxt : x⁻¹ * (t * x * t⁻¹) ∈ D₂) :
    ∃ k ∈ K₂, k⁻¹ * x ∈ D₂ := by
  have hτ : tauG2 h (mk2 D₂ K₂ D₁ ⟨x, hx⟩) = mk2 D₂ K₂ D₁ ⟨x, hx⟩ := by
    rw [tauG2_mk, Y14Hyp.mk2_eq_iff]
    have := D₂.inv_mem hxt
    simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
    convert this using 1
    group
  obtain ⟨g, hg⟩ := hfix _ hτ
  rw [h.theta2_apply, Y14Hyp.mk2_eq_iff] at hg
  exact ⟨θ₂ g, h.K₂_eq ▸ ⟨g, rfl⟩, hg⟩

theorem Y14Hyp.main [Finite G] (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) (F : Type) [Field F]
    [Finite F] (hF : Nat.card F = 4) :
    D₂ ≤ nTwo D₂ K₂ D₁ ∧ nTwo D₂ K₂ D₁ ≤ normalizer (D₂ : Set G) ∧
      t ∈ normalizer ((nTwo D₂ K₂ D₁ : Subgroup G) : Set G) ∧
      (∀ x ∈ nTwo D₂ K₂ D₁, x⁻¹ * (t * x * t⁻¹) ∈ D₂ → x ∈ K₂ ⊔ D₂) ∧
      nTwo D₂ K₂ D₁ ⊓ centralizer ({t} : Set G) = K₂ ⊔ A₂ ∧
      ∃ M : Subgroup G, D₂ ≤ M ∧ M ≤ nTwo D₂ K₂ D₁ ∧
        nTwo D₂ K₂ D₁ = M ⊔ CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t ∧
        ⁅M, CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t⁆ ≤ D₂ ∧
        D₂.relIndex (M ⊓ CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t) ∣ 3 ∧
        ∃ _ : (D₂.subgroupOf M).Normal, ∃ ψ : SL(3, F) →* M ⧸ D₂.subgroupOf M,
          Function.Surjective ψ ∧ ψ.ker ≤ center SL(3, F) := by
  have : Fact (ElemSec D₂ (⊥ : Subgroup G)) := ⟨h.elemSec⟩
  have hN := h.normal_nTwo
  obtain ⟨hfix, X, h1, h2, h3, ψ, hψ, hk, -⟩ := h.r3bHyp.main
  have hcent : ∀ x ∈ nTwo D₂ K₂ D₁, x⁻¹ * (t * x * t⁻¹) ∈ D₂ → ∃ k ∈ K₂, k⁻¹ * x ∈ D₂ :=
    fun x hx hxt => h.centralizer_of_fix hfix hx hxt
  refine ⟨D₂_le_nTwo, h.nTwo_le_normalizer, h.t_mem_normalizer, fun x hx hxt => ?_, ?_,
    h.type_back F hF X h1 h2 h3 ψ hψ hk⟩
  · obtain ⟨k, hk, hkx⟩ := hcent x hx hxt
    have : x = k * (k⁻¹ * x) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hkx)
  · apply le_antisymm
    · rintro x ⟨hx, hxt⟩
      have hxt' : t * x = x * t := (Subgroup.mem_centralizer_singleton_iff.mp hxt).symm
      obtain ⟨k, hk, hkx⟩ := hcent x hx (by
        rw [show t * x * t⁻¹ = x by rw [hxt', mul_inv_cancel_right], inv_mul_cancel]
        exact one_mem _)
      have hkt : t * k⁻¹ = k⁻¹ * t := by
        have := h.K₂_t k hk
        calc t * k⁻¹ = k⁻¹ * (k * t) * k⁻¹ := by group
          _ = k⁻¹ * (t * k) * k⁻¹ := by rw [this]
          _ = k⁻¹ * t := by group
      have hd : k⁻¹ * x ∈ A₂ := h.D₂_H _ hkx (by
        rw [← mul_assoc, hkt, mul_assoc, hxt', mul_assoc])
      have : x = k * (k⁻¹ * x) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hd)
    · refine sup_le (fun k hk => Subgroup.mem_inf.mpr ⟨K₂_le_nTwo hk,
        Subgroup.mem_centralizer_singleton_iff.mpr (h.K₂_t k hk).symm⟩) (fun a ha =>
        Subgroup.mem_inf.mpr ⟨D₂_le_nTwo (h.A₂_le ha),
          Subgroup.mem_centralizer_singleton_iff.mpr (h.A₂_t a ha).symm⟩)

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
