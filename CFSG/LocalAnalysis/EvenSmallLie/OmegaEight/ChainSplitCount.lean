module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Coord

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1

variable {G : Type*} [Group G]

theorem card_le_of_reps [Finite G] {C W : Subgroup G} {Φ : (Fin 6 → ZMod 4) → G}
    (S : Finset (Matrix (Fin 6) (Fin 6) (ZMod 4))) (hrep : ∀ c ∈ C, ∃ F ∈ S, Rep Φ c F)
    (hker : ∀ c ∈ C, Rep Φ c 1 → c ∈ W) :
    Nat.card C ≤ Nat.card (C ⊓ W : Subgroup G) * S.card := by
  classical
  choose f hfS hf using fun c : C => hrep c c.2
  let pick : Matrix (Fin 6) (Fin 6) (ZMod 4) → C := fun F =>
    if h : ∃ c : C, f c = F then Classical.choose h else ⟨1, one_mem C⟩
  have hpick : ∀ c : C, f (pick (f c)) = f c := by
    intro c
    have h : ∃ c' : C, f c' = f c := ⟨c, rfl⟩
    simp only [pick, h, dite_true]
    exact Classical.choose_spec h
  have hrw : ∀ c : C, ((pick (f c) : G))⁻¹ * c ∈ C ⊓ W := by
    intro c
    have hmem : ((pick (f c) : G))⁻¹ * c ∈ C := C.mul_mem (C.inv_mem (pick (f c)).2) c.2
    refine Subgroup.mem_inf.2 ⟨hmem, hker _ hmem fun v => ?_⟩
    have h1 := hf (pick (f c))
    rw [hpick c] at h1
    have h2 := hf c v
    rw [one_mulVec]
    calc ((pick (f c) : G))⁻¹ * c * Φ v * (((pick (f c) : G))⁻¹ * c)⁻¹ =
        ((pick (f c) : G))⁻¹ * (c * Φ v * (c : G)⁻¹) * (pick (f c) : G) := by group
      _ = ((pick (f c) : G))⁻¹ * Φ (f c *ᵥ v) * (pick (f c) : G) := by rw [h2]
      _ = ((pick (f c) : G))⁻¹ * ((pick (f c) : G) * Φ v * ((pick (f c) : G))⁻¹) *
          (pick (f c) : G) := by rw [h1 v]
      _ = Φ v := by group
  let g : C → (C ⊓ W : Subgroup G) × S := fun c => (⟨_, hrw c⟩, ⟨f c, hfS c⟩)
  have hg : Function.Injective g := by
    intro c c' h
    simp only [g, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h2] at h1
    exact Subtype.ext (mul_left_cancel h1)
  have := Nat.card_le_card_of_injective g hg
  rwa [Nat.card_prod, Nat.card_eq_finsetCard] at this

end CFSG.EvenSmallLie.OmegaEight.Chain
