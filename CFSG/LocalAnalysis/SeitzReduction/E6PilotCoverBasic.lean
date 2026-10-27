module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeConj

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

section Generic

variable {X Y Z W : Type*} [Group X] [Group Y] [Group Z] [Group W]

theorem ker_comp_comp_symm (ψ : X ≃* Y) (p : X →* Z) (φ : Z ≃* W) :
    (φ.toMonoidHom.comp (p.comp ψ.symm.toMonoidHom)).ker = p.ker.map ψ.toMonoidHom := by
  ext y
  constructor
  · intro hy
    have hy' : p (ψ.symm y) = 1 := by
      have h := (MonoidHom.mem_ker).1 hy
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
      exact φ.injective (h.trans (map_one φ).symm)
    exact ⟨ψ.symm y, hy', by simp⟩
  · rintro ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [(MonoidHom.mem_ker).1 hx, map_one]

theorem map_le_center_of_le_center (ψ : X ≃* Y) {A : Subgroup X} (hA : A ≤ center X) :
    A.map ψ.toMonoidHom ≤ center Y := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := ψ.surjective y
  have h := mem_center_iff.1 (hA ha) x
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, h]

end Generic

section Cover

variable {K : Type} [Field K] (σ : K ≃+* K) {G : Type} [Group G] {L : Subgroup G}
  (e : L ≃* adjointGroup .E6 (fixSubfield σ))

structure FieldNeighbourCover (N : E6Neighbour) where
  p : neighbourCore e N →* N.levi K
  surjective : Function.Surjective p
  ker_le_center : p.ker ≤ center (neighbourCore e N)
  odd_card_ker : Odd (Nat.card p.ker)
  fix : ∀ x : N.levi (fixSubfield σ), ∃ y : neighbourCore e N,
    (y : G) = ((e.symm (x : adjointGroup .E6 (fixSubfield σ)) : L) : G) ∧
      p y = leviInclusion σ N x

variable {σ e}

@[expose] noncomputable def FieldNeighbourIso.toCover {N : E6Neighbour}
    (h : FieldNeighbourIso σ e N) : FieldNeighbourCover σ e N where
  p := h.Φ.symm.toMonoidHom
  surjective := h.Φ.symm.surjective
  ker_le_center := by
    intro y hy
    have hy' : h.Φ.symm y = h.Φ.symm 1 := by
      rw [map_one]
      exact hy
    rw [h.Φ.symm.injective hy']
    exact one_mem _
  odd_card_ker := by
    have hbot : h.Φ.symm.toMonoidHom.ker = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hy' : h.Φ.symm y = h.Φ.symm 1 := by
        rw [map_one]
        exact hy
      exact (mem_bot).2 (h.Φ.symm.injective hy')
    rw [hbot, card_bot]
    exact odd_one
  fix x := ⟨h.Φ (leviInclusion σ N x), h.fix x, by simp⟩

theorem FieldNeighbourCover.injective_of_ker_eq_bot {N : E6Neighbour}
    (h : FieldNeighbourCover σ e N) (hker : h.p.ker = ⊥) : Function.Injective h.p :=
  (MonoidHom.ker_eq_bot_iff _).1 hker

@[expose] noncomputable def FieldNeighbourCover.toIso {N : E6Neighbour}
    (h : FieldNeighbourCover σ e N) (hker : h.p.ker = ⊥) : FieldNeighbourIso σ e N where
  Φ := (MulEquiv.ofBijective h.p ⟨h.injective_of_ker_eq_bot hker, h.surjective⟩).symm
  fix x := by
    obtain ⟨y, hy, hpy⟩ := h.fix x
    have h1 : (MulEquiv.ofBijective h.p ⟨h.injective_of_ker_eq_bot hker, h.surjective⟩).symm
        (leviInclusion σ N x) = y := by
      rw [MulEquiv.symm_apply_eq]
      exact hpy.symm
    rw [h1]
    exact hy

end Cover

section Neighbour

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

@[expose] noncomputable def FieldNeighbourCover.toNeighbour (h : FieldNeighbourCover σ e .high)
    (N : E6Neighbour) : FieldNeighbourCover σ e N where
  p := (highLeviConjEquiv K N).toMonoidHom.comp
    (h.p.comp (neighbourCoreConjEquiv e N).symm.toMonoidHom)
  surjective := by
    intro z
    obtain ⟨y, hy⟩ := h.surjective ((highLeviConjEquiv K N).symm z)
    refine ⟨neighbourCoreConjEquiv e N y, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hy,
      MulEquiv.apply_symm_apply]
  ker_le_center := by
    rw [ker_comp_comp_symm]
    exact map_le_center_of_le_center _ h.ker_le_center
  odd_card_ker := by
    rw [ker_comp_comp_symm, card_map_of_injective (neighbourCoreConjEquiv e N).injective]
    exact h.odd_card_ker
  fix x := by
    obtain ⟨x₀, rfl⟩ := (highLeviConjEquiv (fixSubfield σ) N).surjective x
    obtain ⟨y₀, hy₀, hpy₀⟩ := h.fix x₀
    refine ⟨neighbourCoreConjEquiv e N y₀, ?_, ?_⟩
    · change ((e.symm (N.rep (fixSubfield σ)) : L) : G) * (y₀ : G) *
          ((e.symm (N.rep (fixSubfield σ)) : L) : G)⁻¹ =
        ((e.symm (N.rep (fixSubfield σ) * (x₀ : adjointGroup .E6 (fixSubfield σ)) *
          (N.rep (fixSubfield σ))⁻¹) : L) : G)
      rw [hy₀, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hpy₀, leviInclusion, leviInclusion, leviBaseChange_highLeviConjEquiv]

theorem FieldNeighbourCover.ker_toNeighbour (h : FieldNeighbourCover σ e .high)
    (N : E6Neighbour) :
    (h.toNeighbour N).p.ker = h.p.ker.map (neighbourCoreConjEquiv e N).toMonoidHom :=
  ker_comp_comp_symm _ _ _

theorem FieldNeighbourCover.ker_toNeighbour_eq_bot (h : FieldNeighbourCover σ e .high)
    (hker : h.p.ker = ⊥) (N : E6Neighbour) : (h.toNeighbour N).p.ker = ⊥ := by
  rw [h.ker_toNeighbour, hker, Subgroup.map_bot]

end Neighbour

end CFSG.SeitzReduction.E6Pilot
