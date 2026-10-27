module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Order.Atoms

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

def supportingMaximals (𝓜 : Set (Subgroup G)) (S : Subgroup G → Subgroup G) (x : G) :
    Set (Subgroup G) :=
  {M ∈ 𝓜 | x ∈ S M}

variable {𝓜 𝓝 : Set (Subgroup G)} {S : Subgroup G → Subgroup G} {M : Subgroup G} {x y : G}

@[simp]
theorem mem_supportingMaximals :
    M ∈ supportingMaximals 𝓜 S x ↔ M ∈ 𝓜 ∧ x ∈ S M := Iff.rfl

theorem supportingMaximals_subset : supportingMaximals 𝓜 S x ⊆ 𝓜 := fun _ hM => hM.1

theorem isCoatom_of_mem_supportingMaximals (h𝓜 : ∀ M ∈ 𝓜, IsCoatom M)
    (hM : M ∈ supportingMaximals 𝓜 S x) : IsCoatom M := h𝓜 M hM.1

theorem mem_of_mem_supportingMaximals (hS : ∀ M ∈ 𝓜, S M ≤ M)
    (hM : M ∈ supportingMaximals 𝓜 S x) : x ∈ M := hS M hM.1 hM.2

@[simp]
theorem supportingMaximals_one : supportingMaximals 𝓜 S 1 = 𝓜 := by
  ext M; simp

@[simp]
theorem supportingMaximals_inv : supportingMaximals 𝓜 S x⁻¹ = supportingMaximals 𝓜 S x := by
  ext M; simp

theorem inter_subset_supportingMaximals_mul :
    supportingMaximals 𝓜 S x ∩ supportingMaximals 𝓜 S y ⊆ supportingMaximals 𝓜 S (x * y) :=
  fun _ h => ⟨h.1.1, mul_mem h.1.2 h.2.2⟩

theorem supportingMaximals_mono (h : 𝓜 ⊆ 𝓝) :
    supportingMaximals 𝓜 S x ⊆ supportingMaximals 𝓝 S x := fun _ hM => ⟨h hM.1, hM.2⟩

theorem supportingMaximals_finite_of_finite (h : 𝓜.Finite) :
    (supportingMaximals 𝓜 S x).Finite := h.subset supportingMaximals_subset

theorem supportingMaximals_finite [Finite G] : (supportingMaximals 𝓜 S x).Finite :=
  Set.toFinite _

end CFSG.FeitThompson
