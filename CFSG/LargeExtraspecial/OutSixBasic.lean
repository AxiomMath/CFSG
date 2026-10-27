module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type*} [Group X]

@[expose] noncomputable def conjOuter (X₀ : Subgroup X) [X₀.Normal] : X →* Outer X₀ :=
  (QuotientGroup.mk' (inner X₀)).comp MulAut.conjNormal

theorem ker_conjOuter (X₀ : Subgroup X) [X₀.Normal] (hC : centralizer (X₀ : Set X) ≤ X₀) :
    (conjOuter X₀).ker = X₀ := by
  ext g
  rw [MonoidHom.mem_ker, conjOuter, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hcent : (x : X)⁻¹ * g ∈ centralizer (X₀ : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      have hxy : (x : X) * y * (x : X)⁻¹ = g * y * g⁻¹ := by
        have := congrArg (fun φ : MulAut X₀ => ((φ ⟨y, hy⟩ : X₀) : X)) hx
        simpa only [MulAut.conj_apply, MulAut.conjNormal_apply, coe_mul, coe_inv] using this
      calc y * ((x : X)⁻¹ * g) = (x : X)⁻¹ * ((x : X) * y * (x : X)⁻¹) * g := by group
        _ = (x : X)⁻¹ * (g * y * g⁻¹) * g := by rw [hxy]
        _ = (x : X)⁻¹ * g * y := by group
    have hg : g = (x : X) * ((x : X)⁻¹ * g) := by group
    rw [hg]
    exact mul_mem x.2 (hC hcent)
  · intro hg
    refine ⟨⟨g, hg⟩, ?_⟩
    ext y
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, coe_mul, coe_inv]

theorem index_dvd_card_outer (X₀ : Subgroup X) [X₀.Normal]
    (hC : centralizer (X₀ : Set X) ≤ X₀) : X₀.index ∣ Nat.card (Outer X₀) := by
  have h := index_ker (conjOuter X₀)
  rw [ker_conjOuter X₀ hC] at h
  rw [h]
  exact card_subgroup_dvd_card (conjOuter X₀).range

theorem index_dvd_card_outer_of_mulEquiv {Y : Type*} [Group Y] (X₀ : Subgroup X) [X₀.Normal]
    (hC : centralizer (X₀ : Set X) ≤ X₀) (e : X₀ ≃* Y) : X₀.index ∣ Nat.card (Outer Y) := by
  rw [← Nat.card_congr (equivalence e).toEquiv]
  exact index_dvd_card_outer X₀ hC

end CFSG.LargeExtraspecial.S14
