module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

theorem exists_mem_of_conj_sylow_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {B : Subgroup G} (hTB : (T : Subgroup G) ≤ B) {y : G}
    (hy : ∀ b ∈ B, y * b * y⁻¹ ∈ B) :
    ∃ b ∈ B, b⁻¹ * y ∈ Subgroup.normalizer ((T : Subgroup G) : Set G) := by
  have hle : ((y • T : Sylow p G) : Subgroup G) ≤ B := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    simpa [MulAut.conj_apply] using hy t (hTB ht)
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B (T.subtype hTB) ((y • T).subtype hle)
  rw [Sylow.smul_subtype] at hb
  have h1 : (b : G) • T = y • T := Sylow.subtype_injective hb
  refine ⟨b, b.2, ?_⟩
  have h2 : ((b : G)⁻¹ * y) • T = T := by
    rw [mul_smul, ← h1, inv_smul_smul]
  have := Sylow.smul_eq_iff_mem_normalizer.1 h2
  simpa using this

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
