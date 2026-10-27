module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import CFSG.Goldschmidt.Steps.Red2Basic

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

theorem le_of_same_conj_of_faithful {G : Type} [Group G] {A L : Subgroup G}
    (hfaith : ∀ a ∈ A, a ≠ 1 → ¬ ∀ x ∈ L, a * x = x * a)
    (hsame : ∀ a ∈ A, ∃ x ∈ A ⊓ L, ∀ y ∈ L, a⁻¹ * y * a = x⁻¹ * y * x) :
    A ≤ L := by
  intro a ha
  obtain ⟨x, hx, hconj⟩ := hsame a ha
  have hc : a * x⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
    CFSG.Goldschmidt.Red2.mul_inv_mem_centralizer_of_conj_eq hconj
  have hcA : a * x⁻¹ ∈ A := A.mul_mem ha (A.inv_mem hx.1)
  have hc1 : a * x⁻¹ = 1 := by
    by_contra hne
    exact hfaith (a * x⁻¹) hcA hne (fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hc y hy).symm)
  have hax : a = x := mul_inv_eq_one.mp hc1
  simpa [hax] using hx.2

end CFSG.GH74.GLS.NT44

end
