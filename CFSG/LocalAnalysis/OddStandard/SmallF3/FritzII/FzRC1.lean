module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRRk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRE32

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem fzrAux_mem_invCent_iff {H : Type*} [Group H] {u g : H} :
    g ∈ invCent u ↔ g * u = u * g := by
  rw [invCent]
  exact Subgroup.mem_centralizer_singleton_iff

theorem fzr_nc_of_E32 (h : Ctx t L S x₁ x₂ lam rho tau) {T₂ : Subgroup G} (hT₂ : IsPGroup 2 T₂)
    (hST : S ≤ T₂) {E : Subgroup G} (hET : E ≤ T₂) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hEsq : ∀ x ∈ E, x * x = 1) (hE32 : Nat.card E = 32) {u : G} (hu : u ∈ E) :
    ¬ ∃ g : G, g⁻¹ * t * g = u := by
  refine fzr_not_conj_of_elem_gt (E := E) h hT₂ hST ?_ ?_ ?_
  · intro e he
    refine ⟨hET he, ?_⟩
    exact (fzrAux_mem_invCent_iff).mpr (hEc e he u hu)
  · refine ⟨⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]
    exact hEsq x hx
  · rw [hE32]; norm_num

theorem fzr_nc_of_mem_X (h : Ctx t L S x₁ x₂ lam rho tau) {T₂ : Subgroup G}
    (hT₂ : IsPGroup 2 T₂) (hST : S ≤ T₂) {X : Subgroup G} (hXT : X ≤ T₂)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXsq : ∀ x ∈ X, x * x = 1)
    (hX16 : Nat.card X = 16) {s : G} (hsT : s ∈ T₂) (hs2 : s * s = 1)
    (hsX : ∀ x ∈ X, s * x = x * s) (hsXn : s ∉ X) {u : G} (hu : u ∈ X) :
    ¬ ∃ g : G, g⁻¹ * t * g = u := by
  obtain ⟨E, hXE, -, hform, hEc, hEsq, hE32⟩ := fzr_E32 hXc hXsq hX16 hs2 hsX hsXn
  have hET : E ≤ T₂ := by
    intro g hg
    obtain ⟨x, hx, rfl | rfl⟩ := hform g hg
    · exact hXT hx
    · exact T₂.mul_mem (hXT hx) hsT
  exact fzr_nc_of_E32 h hT₂ hST hET hEc hEsq hE32 (hXE hu)

theorem fzr_nc_of_cent_X (h : Ctx t L S x₁ x₂ lam rho tau) {T₂ : Subgroup G}
    (hT₂ : IsPGroup 2 T₂) (hST : S ≤ T₂) {X : Subgroup G} (hXT : X ≤ T₂)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXsq : ∀ x ∈ X, x * x = 1)
    (hX16 : Nat.card X = 16) {u : G} (huT : u ∈ T₂) (hu2 : u * u = 1)
    (huX : ∀ x ∈ X, u * x = x * u) (hunX : u ∉ X) :
    ¬ ∃ g : G, g⁻¹ * t * g = u := by
  obtain ⟨E, hXE, huE, hform, hEc, hEsq, hE32⟩ := fzr_E32 hXc hXsq hX16 hu2 huX hunX
  have hET : E ≤ T₂ := by
    intro g hg
    obtain ⟨x, hx, rfl | rfl⟩ := hform g hg
    · exact hXT hx
    · exact T₂.mul_mem (hXT hx) huT
  exact fzr_nc_of_E32 h hT₂ hST hET hEc hEsq hE32 huE

end CFSG.OddStandard.SmallF3.FritzII
