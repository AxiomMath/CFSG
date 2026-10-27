module


public import Mathlib.RepresentationTheory.Basic
public import CFSG.GroupTheory.AutomorphismAction.CommutingPGroup

public section

namespace CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors

theorem exists_fixed {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (W : Submodule (ZMod 2) V)
    (hW : ∀ g : H, W ≤ W.comap (ρ g)) (hne : W ≠ ⊥) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ g : H, ρ g v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let S : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (Set.range fun g : H => ρ g w)
  have hSW : S ≤ W := Submodule.span_le.mpr (by
    rintro _ ⟨g, rfl⟩
    exact hW g hwW)
  have hSinv : ∀ g : H, ∀ u ∈ S, ρ g u ∈ S := by
    intro g u hu
    have : S ≤ S.comap (ρ g) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show ρ g (ρ k w) ∈ S
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * k, rfl⟩
    exact this hu
  haveI : Finite (Set.range fun g : H => ρ g w) := Set.finite_range _
  haveI : Module.Finite (ZMod 2) S := Module.Finite.span_of_finite _ (Set.finite_range _)
  haveI : Finite S := Module.finite_of_finite (ZMod 2)
  let σ : H →* (S ≃ₗ[ZMod 2] S) :=
    { toFun := fun g =>
        LinearEquiv.ofLinear ((ρ g).restrict fun u hu => hSinv g u hu)
          ((ρ g⁻¹).restrict fun u hu => hSinv g⁻¹ u hu)
          (by
            ext u
            show ρ g (ρ g⁻¹ (u : V)) = u
            rw [← Module.End.mul_apply, ← map_mul]; simp)
          (by
            ext u
            show ρ g⁻¹ (ρ g (u : V)) = u
            rw [← Module.End.mul_apply, ← map_mul]; simp)
      map_one' := by ext u; simp
      map_mul' := fun a b => by ext u; simp }
  have hσ : ∀ g (u : S), ((σ g u : S) : V) = ρ g u := fun _ _ => rfl
  let N : Submodule (ZMod 2) S := ⊤
  obtain ⟨u, -, hu0, hu⟩ :=
    CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.exists_fixed_of_invariant hH σ N
    (fun _ _ _ => trivial) (by
      intro h
      have : (⟨w, Submodule.subset_span ⟨1, by simp⟩⟩ : S) ∈ N := trivial
      rw [h] at this
      apply hw0
      simpa using congrArg Subtype.val ((Submodule.mem_bot _).1 this))
  refine ⟨u, hSW u.2, fun h => hu0 (Subtype.ext h), fun g => ?_⟩
  have := congrArg Subtype.val (hu g)
  simpa [hσ] using this

end CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors
