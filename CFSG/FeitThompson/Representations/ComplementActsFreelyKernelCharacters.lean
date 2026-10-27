module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.FeitThompson.Representations.BrauerPermutationLemma
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.ComplementFixesNoKernelClass

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct

variable {H E : Type*} [Group H] [Group E] {φ : E →* MulAut H} {u : E}

theorem card_fixed_conjClasses_eq_one [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) (hu : u ≠ 1) :
    Nat.card {K : ConjClasses H // conjClassesAut (φ u) K = K} = 1 := by
  have h : Nat.card {K : ConjClasses H // conjClassesAut (φ u) K = K}
      = Nat.card {K : ConjClasses H // K = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun K =>
      (conjClassesAut_eq_self_iff (φ u) K).trans
        ((conjClasses_map_eq_self_iff (φ u) K).symm.trans
          (conjClasses_map_eq_self_iff_eq_one hφ hu K)))
  rw [h]
  exact Nat.card_unique

theorem card_fixed_Irr_eq_one [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) (hu : u ≠ 1) :
    Nat.card {χ : Irr H // irrAut (φ u) χ = χ} = 1 := by
  rw [card_fixed_irrAut_eq_card_fixed_conjClassesAut (φ u)]
  exact card_fixed_conjClasses_eq_one hφ hu

theorem eq_one_of_comp_eq_self_of_ne_one [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1) (h : ∀ x : H, θ (φ u x) = θ x) : u = 1 := by
  by_contra hu
  have hsub : Subsingleton {χ : Irr H // irrAut (φ u) χ = χ} :=
    (Nat.card_eq_one_iff_unique.1 (card_fixed_Irr_eq_one hφ hu)).1
  have h1 : irrAut (φ u) (⟨θ, hθ⟩ : Irr H) = ⟨θ, hθ⟩ := (irrAut_eq_self_iff _ _).2 h
  have h2 : irrAut (φ u) (⟨1, one_mem_Irr⟩ : Irr H) = ⟨1, one_mem_Irr⟩ :=
    (irrAut_eq_self_iff _ _).2 fun _ => rfl
  have := hsub.allEq ⟨⟨θ, hθ⟩, h1⟩ ⟨⟨1, one_mem_Irr⟩, h2⟩
  exact hθ1 (congrArg (fun z => (z.1 : H → ℂ)) this)

theorem irrAut_eq_self_iff_eq_one [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) {θ : Irr H}
    (hθ1 : (θ : H → ℂ) ≠ 1) : irrAut (φ u) θ = θ ↔ u = 1 := by
  refine ⟨fun h => eq_one_of_comp_eq_self_of_ne_one hφ θ.2 hθ1 ((irrAut_eq_self_iff _ _).1 h), ?_⟩
  rintro rfl
  simp

theorem stabilizer_setOf_eq_singleton_one [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1) :
    {v : E | ∀ x : H, θ (φ v x) = θ x} = {1} := by
  ext v
  refine ⟨fun h => eq_one_of_comp_eq_self_of_ne_one hφ hθ hθ1 h, ?_⟩
  rintro rfl x
  simp

theorem eq_one_of_conj_inr_invariant [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1)
    (h : ∀ x y : H, (inl y : H ⋊[φ] E) = inr u * inl x * (inr u)⁻¹ → θ y = θ x) : u = 1 :=
  eq_one_of_comp_eq_self_of_ne_one hφ hθ hθ1 fun x =>
    h x (φ u x) (inr_mul_inl_mul_inr_inv u x).symm

end CFSG.FeitThompson
