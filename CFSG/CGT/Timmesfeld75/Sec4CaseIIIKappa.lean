module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB2

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Aux

variable {G : Type} [Group G]

theorem z_fixes_a {ℓ ℓ₁ a t t₁ t₂ : G} (hℓ : ℓ * ℓ = 1) (hℓ₁ : ℓ₁ * ℓ₁ = 1)
    (hℓℓ₁ : ℓ * ℓ₁ = ℓ₁ * ℓ) (htℓ : t * ℓ * t⁻¹ = ℓ) (hta : t * a * t⁻¹ = ℓ * a)
    (ht₁ℓ : t₁ * ℓ * t₁⁻¹ = ℓ₁ * ℓ) (ht₁a : t₁ * a * t₁⁻¹ = ℓ₁ * a)
    (ht₂a : t₂ * a * t₂⁻¹ = a) :
    (t₂ * t * t₁ * t) * a * (t₂ * t * t₁ * t)⁻¹ = a := by
  have c2 : ℓ₁ * ℓ * ℓ₁ = ℓ := by
    calc ℓ₁ * ℓ * ℓ₁ = ℓ * ℓ₁ * ℓ₁ := by rw [← hℓℓ₁]
      _ = ℓ := by rw [mul_assoc, hℓ₁, mul_one]
  have hconj : (t₂ * t * t₁ * t) * a * (t₂ * t * t₁ * t)⁻¹ =
      t₂ * (t * (t₁ * (t * a * t⁻¹) * t₁⁻¹) * t⁻¹) * t₂⁻¹ := by group
  have hmul : ∀ (g x y : G), g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
    intro g x y
    group
  rw [hconj, hta, hmul t₁ ℓ a, ht₁ℓ, ht₁a]
  have e3 : ℓ₁ * ℓ * (ℓ₁ * a) = ℓ * a := by
    calc ℓ₁ * ℓ * (ℓ₁ * a) = (ℓ₁ * ℓ * ℓ₁) * a := by group
      _ = ℓ * a := by rw [c2]
  rw [e3, hmul t ℓ a, htℓ, hta]
  have e5 : ℓ * (ℓ * a) = a := by rw [← mul_assoc, hℓ, one_mul]
  rw [e5, ht₂a]

end Aux

section Helpers

variable {G : Type} [Group G] {U V : Subgroup G}

theorem mem_normalizer_normIn_of_mem {κ : G} (hU : κ ∈ Subgroup.normalizer (U : Set G))
    (hV : κ ∈ Subgroup.normalizer (V : Set G)) :
    κ ∈ Subgroup.normalizer (normIn U V : Set G) := by
  apply mem_normalizer_of_conjSubgroup_eq
  have := normIn_conj κ U V
  rw [mem_normalizer_iff_conjSubgroup_eq.1 hU, mem_normalizer_iff_conjSubgroup_eq.1 hV] at this
  exact this.symm

theorem comm_mem_normIn_of_index_two [Finite G] {κ : G}
    (hU : κ ∈ Subgroup.normalizer (U : Set G)) (hV : κ ∈ Subgroup.normalizer (V : Set G))
    (hcard : Nat.card U = Nat.card (normIn U V) * 2) :
    ∀ y ∈ U, κ * y * κ⁻¹ * y⁻¹ ∈ normIn U V := fun y hy =>
  commutator_mem_of_index_two (normIn_le U V) hcard
    (fun y hy => conj_mem_of_mem_normalizer hU hy)
    (fun y hy => conj_mem_of_mem_normalizer (mem_normalizer_normIn_of_mem hU hV) hy)
    (fun y hy => by
      simpa using conj_mem_of_mem_normalizer
        ((Subgroup.normalizer _).inv_mem (mem_normalizer_normIn_of_mem hU hV)) hy) hy

theorem conj_mem_normIn_of_mem {κ : G} (hU : κ ∈ Subgroup.normalizer (U : Set G))
    (hV : κ ∈ Subgroup.normalizer (V : Set G)) :
    ∀ v ∈ normIn V U, κ * v * κ⁻¹ ∈ normIn V U := fun _ hv =>
  conj_mem_of_mem_normalizer (mem_normalizer_normIn_of_mem hV hU) hv

end Helpers

end CFSG.CGT.Timmesfeld75
