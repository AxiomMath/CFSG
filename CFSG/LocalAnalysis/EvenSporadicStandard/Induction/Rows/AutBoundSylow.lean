module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem conj_mem_of_closed [Finite G] (gens E : Set G)
    (hE : ∀ e ∈ E, ∀ g ∈ gens, g * e * g⁻¹ ∈ E) :
    ∀ h ∈ Subgroup.closure gens, ∀ e ∈ E, h * e * h⁻¹ ∈ E := by
  intro h hh e he
  have hh' : h ∈ Submonoid.closure gens := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hh
  clear hh
  induction hh' using Submonoid.closure_induction_left with
  | one => simpa using he
  | mul_left x hx y _ ih =>
    have := hE _ ih x hx
    simpa [mul_assoc] using this

theorem exists_conj_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G) {z : G}
    (hz : orderOf z = p) : ∃ g : G, g * z * g⁻¹ ∈ (T : Subgroup G) := by
  have hQ : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  refine ⟨g, ?_⟩
  have hzS : z ∈ (S : Subgroup G) := hS (Subgroup.mem_zpowers z)
  have h1 := Subgroup.smul_mem_pointwise_smul z (MulAut.conj g) (S : Subgroup G) hzS
  have h2 : (↑(g • S) : Subgroup G) = MulAut.conj g • (S : Subgroup G) := Sylow.coe_subgroup_smul
  rw [← h2, hg] at h1
  simpa using h1

theorem cover_of_sylow [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G) (S : Set G)
    (hS : ∀ n z, z ∈ S → n * z * n⁻¹ ∈ S)
    (hT : ∀ z ∈ (T : Subgroup G), orderOf z = p → z ∈ S) :
    ∀ z : G, orderOf z = p → z ∈ S := by
  intro z hz
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow T hz
  have hord : orderOf (g * z * g⁻¹) = p := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
    simpa [hz] using this
  have h1 := hS g⁻¹ _ (hT _ hg hord)
  simpa [mul_assoc] using h1

end CFSG.EvenSporadicStandard.Induction.AutBound
