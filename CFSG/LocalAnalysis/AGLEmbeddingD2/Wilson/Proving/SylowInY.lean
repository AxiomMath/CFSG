module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

theorem exists_conj_sylow_in_ne [Finite G] (Y : Subgroup G) (R R' : Sylow p Y) (hne : R' ≠ R) :
    ∃ y ∈ Y, y ∉ normalizer ((R : Subgroup Y).map Y.subtype) ∧
      ∀ x : G, x ∈ (R' : Subgroup Y).map Y.subtype ↔
        y⁻¹ * x * y ∈ (R : Subgroup Y).map Y.subtype := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y R R'
  have hcoe : ∀ z : Y, z ∈ (R' : Subgroup Y) ↔ g⁻¹ * z * g ∈ (R : Subgroup Y) := by
    intro z
    rw [← hg, Sylow.coe_subgroup_smul]
    simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mul_assoc]
  have hmem : ∀ (H : Subgroup Y) (z : Y), (z : G) ∈ H.map Y.subtype ↔ z ∈ H :=
    fun H z => Subgroup.mem_map_iff_mem Y.subtype_injective
  have hout : ∀ (H : Subgroup Y) (x : G), x ∉ Y → x ∉ H.map Y.subtype := by
    intro H x hx hm
    obtain ⟨z, _, hz⟩ := Subgroup.mem_map.mp hm
    exact hx (hz ▸ z.2)
  refine ⟨(g : G), g.2, ?_, ?_⟩
  · intro hn
    apply hne
    apply Sylow.ext
    ext z
    rw [hcoe z, ← hmem (R : Subgroup Y) (g⁻¹ * z * g)]
    have hn' := Subgroup.mem_normalizer_iff.mp hn (((g⁻¹ * z * g : Y)) : G)
    have e : (g : G) * (((g⁻¹ * z * g : Y)) : G) * (g : G)⁻¹ = (z : G) := by
      simp [mul_assoc]
    rw [hn', e, hmem]
  · intro x
    by_cases hx : x ∈ Y
    · lift x to Y using hx with z
      have e : (g : G)⁻¹ * (z : G) * (g : G) = ((g⁻¹ * z * g : Y) : G) := by
        simp
      rw [e, hmem, hmem, hcoe]
    · constructor
      · intro h; exact absurd h (hout _ _ hx)
      · intro h
        exfalso
        obtain ⟨z, _, hz⟩ := Subgroup.mem_map.mp h
        have hz' : (z : G) = (g : G)⁻¹ * x * (g : G) := hz
        apply hx
        have : x = (g : G) * (z : G) * (g : G)⁻¹ := by rw [hz']; group
        rw [this]
        exact Y.mul_mem (Y.mul_mem g.2 z.2) (Y.inv_mem g.2)

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
