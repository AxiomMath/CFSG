module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem card_modEq_one_of_isPGroup_normalizes_of_inf_centralizer_eq_bot
    {p : ℕ} [Fact p.Prime] {X W : Subgroup G} (hX : IsPGroup p X)
    (hXW : X ≤ normalizer (W : Set G))
    (hC : W ⊓ centralizer (X : Set G) = ⊥) :
    Nat.card W ≡ 1 [MOD p] := by
  classical
  let _ : MulAction X W :=
    MulAction.compHom W ((W.normalizerMonoidHom).comp (Subgroup.inclusion hXW))
  have hfix : MulAction.fixedPoints X W = {1} := by
    ext w
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hw
      have hwC : (w : G) ∈ W ⊓ centralizer (X : Set G) := by
        refine ⟨w.2, mem_centralizer_iff.2 fun x hx => ?_⟩
        have h1 : (x : G) * (w : G) * (x : G)⁻¹ = w := by
          have h1' : (W.normalizerMonoidHom (Subgroup.inclusion hXW ⟨x, hx⟩)) w = w :=
            hw ⟨x, hx⟩
          have h1'' : ((W.normalizerMonoidHom (Subgroup.inclusion hXW ⟨x, hx⟩)) w : G) =
              (w : G) := congrArg Subtype.val h1'
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1''
          exact h1''
        calc (x : G) * (w : G) = (x : G) * (w : G) * (x : G)⁻¹ * (x : G) := by group
          _ = (w : G) * (x : G) := by rw [h1]
      rw [hC, mem_bot] at hwC
      exact Subtype.ext hwC
    · rintro rfl x
      exact map_one (W.normalizerMonoidHom (Subgroup.inclusion hXW x))
  have hmod := hX.card_modEq_card_fixedPoints W
  rwa [hfix, Nat.card_unique (α := ↥({1} : Set W))] at hmod

end CFSG.GroupTheory
