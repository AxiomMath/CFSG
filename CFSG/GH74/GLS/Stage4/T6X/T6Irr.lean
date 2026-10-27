module

public import CFSG.GH74.GLS.Stage4.T6Aut
public import CFSG.GH74.GLS.Stage4.T6Aut3
public import CFSG.GH74.GLS.Stage4.T6Grp

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6X

open CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem t6_map_comap {φ : SL2 F →* G} {Y : Subgroup G} (h : Y ≤ φ.range) : (Y.comap φ).map φ = Y :=
  Subgroup.map_comap_eq_self h

theorem t6_irr_u {φ : SL2 F →* G} (hφ : Function.Injective φ) (hodd : Odd (Nat.card F))
    {Y : Subgroup G} (hY : Y ≤ (uSub F).map φ)
    (hT : ∀ t ∈ tSub F, ∀ y ∈ Y, φ t * y * (φ t)⁻¹ ∈ Y) : Y = ⊥ ∨ Y = (uSub F).map φ := by
  have hYr : Y ≤ φ.range := hY.trans (Subgroup.map_le_range φ _)
  have hY' : Y.comap φ ≤ uSub F := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hY hy
    have : x = y := hφ hxy
    rwa [this] at hx
  have hT' : ∀ t ∈ tSub F, ∀ y ∈ Y.comap φ, t * y * t⁻¹ ∈ Y.comap φ := by
    intro t ht y hy
    have := hT t ht (φ y) hy
    simpa [Subgroup.mem_comap] using this
  rcases t6_torus_inv_u hodd _ hY' hT' with h | h
  · left
    rw [← t6_map_comap hYr, h]; simp
  · right
    rw [← t6_map_comap hYr, h]

theorem t6_aut_X {φ : SL2 F →* G} (hφ : Function.Injective φ) (hodd : Odd (Nat.card F))
    (h3 : 3 ≤ Nat.card F) {y : G} (hy : ∀ g ∈ φ.range, y * g * y⁻¹ ∈ φ.range)
    (hyX : ∀ c : F, y * φ (sl2U c) * y⁻¹ = φ (sl2U c)) :
    ∃ s : F, ∀ g : SL2 F, y * φ g * y⁻¹ = φ (sl2U s) * φ g * (φ (sl2U s))⁻¹ := by
  have : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hyn : y ∈ normalizer (φ.range : Set G) := Subgroup.mem_normalizer_fintype (fun n hn => hy n hn)
  let ρ : MulAut ↥φ.range := Subgroup.normalizerMonoidHom φ.range ⟨y, hyn⟩
  have hρ : ∀ g : ↥φ.range, ((ρ g : ↥φ.range) : G) = y * g * y⁻¹ := fun g => rfl
  let eφ : SL2 F ≃* ↥φ.range := MonoidHom.ofInjective hφ
  have heφ : ∀ g : SL2 F, ((eφ g : ↥φ.range) : G) = φ g := fun g => rfl
  let α : MulAut (SL2 F) := eφ.trans (ρ.trans eφ.symm)
  have hα : ∀ g : SL2 F, φ (α g) = y * φ g * y⁻¹ := by
    intro g
    have h1 : eφ (α g) = ρ (eφ g) := by
      show eφ (eφ.symm (ρ (eφ g))) = ρ (eφ g)
      exact eφ.apply_symm_apply _
    have h2 := congrArg (fun x : ↥φ.range => (x : G)) h1
    simpa [heφ, hρ] using h2
  have hαfix : ∀ c : F, α (sl2U c) = sl2U c := by
    intro c
    apply hφ
    rw [hα, hyX]
  obtain ⟨s, hs⟩ : ∃ s : F, ∀ g : SL2 F, α g = sl2U s * g * (sl2U s)⁻¹ := by
    rcases h3.eq_or_lt with h | h
    · exact t6_aut_fix_u3 h.symm α hαfix
    · exact t6_aut_fix_u hodd h α hαfix
  refine ⟨s, fun g => ?_⟩
  rw [← hα, hs]
  simp [map_mul, map_inv]

end CFSG.GH74.GLS.Stage4.Rest.T6X
