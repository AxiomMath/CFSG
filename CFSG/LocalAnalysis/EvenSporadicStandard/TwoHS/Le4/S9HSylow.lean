module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_conj_of_card_le [Finite G] {N S₀ S₁ : Subgroup G}
    (hS₀N : S₀ ≤ N) (hS₁N : S₁ ≤ N) (hp₀ : IsPGroup 2 S₀) (hrel : ¬ 2 ∣ S₀.relIndex N)
    (hp₁ : IsPGroup 2 S₁) (hcard : Nat.card S₀ ≤ Nat.card S₁) :
    ∃ g ∈ N, ∀ x : G, x ∈ S₁ ↔ g * x * g⁻¹ ∈ S₀ := by
  set P₀ : Subgroup N := S₀.subgroupOf N with hP₀def
  set P₁ : Subgroup N := S₁.subgroupOf N with hP₁def
  have hP₀ : IsPGroup 2 P₀ := hp₀.of_equiv (subgroupOfEquivOfLe hS₀N).symm
  have hP₁ : IsPGroup 2 P₁ := hp₁.of_equiv (subgroupOfEquivOfLe hS₁N).symm
  let Q₀ : Sylow 2 N := hP₀.toSylow hrel
  obtain ⟨Q₁, hQ₁⟩ := hP₁.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Q₁ Q₀
  have hle : P₁.map (MulAut.conj g).toMonoidHom ≤ P₀ := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 : (MulAut.conj g) z ∈ MulAut.conj g • (Q₁ : Subgroup N) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ₁ hz)
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact h1
  have hcard' : Nat.card P₀ ≤ Nat.card (P₁.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Nat.card_congr (subgroupOfEquivOfLe hS₀N).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hS₁N).toEquiv]
    exact hcard
  have heq : P₁.map (MulAut.conj g).toMonoidHom = P₀ := Subgroup.eq_of_le_of_card_ge hle hcard'
  have hiff : ∀ z : N, z ∈ P₁ ↔ g * z * g⁻¹ ∈ P₀ := by
    intro z
    constructor
    · intro hz
      exact hle ⟨z, hz, rfl⟩
    · intro hz
      rw [← heq] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      have : w = z := (MulAut.conj g).injective hwz
      exact this ▸ hw
  refine ⟨(g : G), g.2, fun x => ?_⟩
  constructor
  · intro hx
    have := (hiff ⟨x, hS₁N hx⟩).1 ((Subgroup.mem_subgroupOf).2 hx)
    exact (Subgroup.mem_subgroupOf.1 this)
  · intro hx
    have hxN : x ∈ N := by
      have h1 : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) ∈ N :=
        N.mul_mem (N.mul_mem (N.inv_mem g.2) (hS₀N hx)) g.2
      simpa [mul_assoc] using h1
    have := (hiff ⟨x, hxN⟩).2 ((Subgroup.mem_subgroupOf).2 hx)
    exact Subgroup.mem_subgroupOf.1 this

end CFSG.EvenSporadicStandard.TwoHS
