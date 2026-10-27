module

public import CFSG.ClassicalInvolution.SmallCases.DSplitDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

section Transport

variable {G G' : Type} [Group G] [Group G'] [Finite G] (φ : G →* G') (hφ : Function.Injective φ)
include hφ

theorem E3.mem_RSet_map {Ω : Set (Subgroup G)} {Ω' : Set (Subgroup G')}
    (hΩ : ∀ X ∈ Ω, X.map φ ∈ Ω') {P : Subgroup G} (hP : P ∈ RSet Ω) : P.map φ ∈ RSet Ω' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J, hJ, Q, rfl⟩ := hP
  let eJ := J.equivMapOfInjective φ hφ
  have hsurj : Function.Surjective eJ.toMonoidHom := eJ.surjective
  refine ⟨J.map φ, hΩ J hJ, Q.mapSurjective hsurj, ?_⟩
  show _ = ((Q : Subgroup J).map eJ.toMonoidHom).map (J.map φ).subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem E3.mem_USet_map {Ω : Set (Subgroup G)} {Ω' : Set (Subgroup G')}
    (hΩ : ∀ X ∈ Ω, X.map φ ∈ Ω') {U : Subgroup G} (hU : U ∈ USet Ω) : U.map φ ∈ USet Ω' := by
  obtain ⟨P, hP, hUP, hcyc, hidx⟩ := hU
  refine ⟨P.map φ, E3.mem_RSet_map φ hφ hΩ hP, Subgroup.map_mono hUP,
    (U.equivMapOfInjective φ hφ).isCyclic.mp hcyc, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
  exact hidx

theorem E3.mem_omegaNbr_map {Ω : Set (Subgroup G)} {Ω' : Set (Subgroup G')}
    (hΩ : ∀ X ∈ Ω, X.map φ ∈ Ω') {K J : Subgroup G} (h : J ∈ omegaNbr Ω K) :
    J.map φ ∈ omegaNbr Ω' (K.map φ) := by
  obtain ⟨hJ, hne, P, hP, hPJ, hPN⟩ := h
  exact ⟨hΩ J hJ, fun h => hne (Subgroup.map_injective hφ h), P.map φ, E3.mem_RSet_map φ hφ hΩ hP,
    Subgroup.map_mono hPJ, (Subgroup.map_mono hPN).trans (Subgroup.le_normalizer_map φ)⟩

theorem E3.mem_omegaStarNbr_map {Ω : Set (Subgroup G)} {Ω' : Set (Subgroup G')}
    (hΩ : ∀ X ∈ Ω, X.map φ ∈ Ω') {K J : Subgroup G} (h : J ∈ omegaStarNbr Ω K) :
    J.map φ ∈ omegaStarNbr Ω' (K.map φ) := by
  obtain ⟨hJ, hne, U, hU, hUJ, hUN⟩ := h
  exact ⟨hΩ J hJ, fun h => hne (Subgroup.map_injective hφ h), U.map φ, E3.mem_USet_map φ hφ hΩ hU,
    Subgroup.map_mono hUJ, (Subgroup.map_mono hUN).trans (Subgroup.le_normalizer_map φ)⟩

theorem E3.dAdj_map {Ω : Set (Subgroup G)} {Ω' : Set (Subgroup G')}
    (hΩ : ∀ X ∈ Ω, X.map φ ∈ Ω') {K J : Subgroup G} (h : Disconnected.dAdj Ω K J) :
    Disconnected.dAdj Ω' (K.map φ) (J.map φ) := by
  rcases h with h | h
  · exact Or.inl (E3.mem_omegaNbr_map φ hφ hΩ h)
  · exact Or.inr (E3.mem_omegaNbr_map φ hφ hΩ h)

end Transport

theorem E3.map_conjSub {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (g : G)
    (K : Subgroup G) : (conjSub g K).map φ = conjSub (φ g) (K.map φ) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

end CFSG.ClassicalInvolution.Q3.TL4
