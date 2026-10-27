module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLModels
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLOrth
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSym
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Module CFSG.ComponentClassification.OutcomeLocal
open scoped commutatorElement

theorem models_of_shape {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hn : 1 ≤ Module.finrank (ZMod 2) W)
    (H L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
    (hgen : ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) W),
      (∀ t ∈ S, IsF2Transvection t) ∧ H = Subgroup.closure S)
    (hirr : ∀ U : Submodule (ZMod 2) W,
      (∀ g ∈ H, ∀ u ∈ U, (g : W →ₗ[ZMod 2] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hLH : L ≤ H) (hidx : L.relIndex H = 2) (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) :
    (∃ m, IsOmegaPlusModel L m) ∨ (∃ m, IsOmegaMinusModel L m) ∨ ∃ m, IsAltModel L m := by
  have h3 : 3 ≤ finrank (ZMod 2) W := by
    by_contra hlt
    exact hL1 (eq_bot_of_isPerfect_of_finrank_le_two (by omega) L hperf)
  obtain ⟨hLeq, hcases⟩ := shape_of_perfect_index_two hn H L hgen hirr hLH hidx hperf hL1
  rcases hcases with ⟨h4, f, hnd, halt, hH⟩ | ⟨Q, hQ, hH⟩ | ⟨he, hsym⟩
  · obtain ⟨β, hβ⟩ := exists_heartSix_of_symplectic_four f hnd halt h4
      (heartRep_injective (by norm_num))
    exact Or.inr (Or.inr ⟨6, isAltModel_of_heart (by norm_num) β (by rw [hH]; exact hβ) hLeq⟩)
  · rcases isOmegaModel_of_orth Q hQ (T := L) (by rw [hLeq, hH]; rfl) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨k, hk⟩ := he
    rcases hsym with ⟨β, hβ⟩ | ⟨β, hβ⟩
    · exact Or.inr (Or.inr ⟨finrank (ZMod 2) W + 1,
        isAltModel_of_sumZero (by omega) ⟨k, by omega⟩ β hβ hLeq⟩)
    · exact Or.inr (Or.inr ⟨finrank (ZMod 2) W + 2,
        isAltModel_of_heart (by omega) β hβ hLeq⟩)

section Rep

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {M : Type*} [Group M]

theorem models_of_transvection_rep [Nontrivial W]
    (ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2) W) (L : Subgroup M) [L.Normal] (s : M)
    (hirr : ∀ P : Submodule (ZMod 2) W,
      (∀ m : M, ∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤)
    (htr : IsF2Transvection (ρ s))
    (hgen : ∀ T : Subgroup M, T.Normal → ρ.ker ≤ T → s ∈ T → T = ⊤)
    (hM : ⊤ ≤ L ⊔ Subgroup.zpowers s ⊔ ρ.ker)
    (hperf : L ≤ ⁅L, L⁆ ⊔ ρ.ker) (hL1 : ¬ L ≤ ρ.ker) (hs : ρ s ∉ L.map ρ) :
    (∃ m, IsOmegaPlusModel (L.map ρ) m) ∨ (∃ m, IsOmegaMinusModel (L.map ρ) m) ∨
      ∃ m, IsAltModel (L.map ρ) m := by
  refine models_of_shape Module.finrank_pos ρ.range (L.map ρ)
    ⟨_, ?_, range_eq_closure_conj ρ s hgen⟩ ?_ (Subgroup.map_le_range ρ L)
    (relIndex_map_eq_two ρ L s htr hM hs) ?_ ?_
  · rintro _ ⟨g, -, rfl⟩
    exact isF2Transvection_conj htr g
  · intro P hP
    refine hirr P fun m w hw => hP (ρ m) ⟨m, rfl⟩ w hw
  · apply le_antisymm
    · exact Subgroup.commutator_le.mpr fun x hx y hy => by
        have : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    · calc L.map ρ ≤ (⁅L, L⁆ ⊔ ρ.ker).map ρ := Subgroup.map_mono hperf
        _ = ⁅L.map ρ, L.map ρ⁆ := by
          rw [Subgroup.map_sup, Subgroup.map_commutator,
            (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  · intro h
    exact hL1 (Subgroup.map_eq_bot_iff _ |>.mp h)

end Rep

end CFSG.HardMathSupport.Cooperstein.StructureLie
