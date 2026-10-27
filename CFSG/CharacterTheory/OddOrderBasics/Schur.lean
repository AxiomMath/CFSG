module

public import CFSG.CharacterTheory.Blocks.Defs

public section

namespace CFSG.OddOrderBasics

theorem complex_irreducible_commuting_scalar {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible)
    (T : Module.End ℂ V) (hT : ∀ g : G, T ∘ₗ ρ g = ρ g ∘ₗ T) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  let f : Representation.IntertwiningMap ρ ρ := { T with isIntertwining' := hT }
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 f
  refine ⟨c, ?_⟩
  ext v
  have h := congrArg (fun φ : Representation.IntertwiningMap ρ ρ => φ v) hc
  simp only [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.coe_one,
    id_eq] at h
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  exact h.symm

theorem abelian_irreducible_character_linear {H : Type} [CommGroup H] (θ : H → ℂ)
    (hθ : θ ∈ BlocksIrr H) : θ 1 = 1 := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hθ
  have : IsMulCommutative H := ⟨⟨mul_comm⟩⟩
  have hdim := Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  rw [Representation.char_one, hdim, Nat.cast_one]

end CFSG.OddOrderBasics
