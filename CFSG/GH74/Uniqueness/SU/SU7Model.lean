module

public import CFSG.GH74.Uniqueness.SU.SU5J2Emb2

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Model

open Subgroup CFSG.GH74.Uniqueness.SU.SU5

theorem sq_mem_U : ∀ s : J2Syl, s ∈ J2Syl.W → s * s ∈ J2Syl.U := by decide +kernel

theorem sq_mem_R : ∀ s : J2Syl,
    ((s * s) * (s * s) = 1 ∧ (s * s ∈ J2Syl.U ∨ s * s ∉ J2Syl.W)) ∨
      (s * s) * (s * s) = J2Syl.z0 := by decide +kernel

theorem gen_R : ∀ r : J2Syl, r * r = J2Syl.z0 → ∃ s : J2Syl, s * s = 1 ∧ s ≠ 1 ∧ s ≠ J2Syl.z0 ∧
    (s ∈ J2Syl.U ∨ s ∉ J2Syl.W) ∧ (s⁻¹ * r) * (s⁻¹ * r) = 1 ∧ s⁻¹ * r ≠ 1 ∧
      s⁻¹ * r ≠ J2Syl.z0 ∧ (s⁻¹ * r ∈ J2Syl.U ∨ s⁻¹ * r ∉ J2Syl.W) := by decide +kernel

theorem faithful_R : ∀ s : J2Syl,
    (∀ r : J2Syl, ((r * r = 1 ∧ (r ∈ J2Syl.U ∨ r ∉ J2Syl.W)) ∨ r * r = J2Syl.z0) →
      (s * r * s⁻¹ * r⁻¹ = 1 ∨ s * r * s⁻¹ * r⁻¹ = J2Syl.z0)) →
    ((s * s = 1 ∧ (s ∈ J2Syl.U ∨ s ∉ J2Syl.W)) ∨ s * s = J2Syl.z0) := by decide +kernel

section Transport

variable {G : Type*} [Group G] {S T : Subgroup G} {x : G}

theorem sq_mem_Zc (h : J2Emb S T x) : ∀ y ∈ T, y * y ∈ Zc T := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  rintro _ ⟨m, hm, rfl⟩
  rw [Zc_map hf, J2Syl.Zc_W, ← map_mul]
  exact Subgroup.mem_map_of_mem f (sq_mem_U m hm)

theorem sq_mem_Rp (h : J2Emb S T x) {z : G} (hz : IsZGen S z) : ∀ s ∈ S,
    ((s * s) * (s * s) = 1 ∧ (s * s ∈ Zc T ∨ s * s ∉ T)) ∨ (s * s) * (s * s) = z := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  obtain rfl := hz.unique (isZGen_f hf)
  rintro _ ⟨m, rfl⟩
  have key : ∀ y : J2Syl, f y ∈ Zc (J2Syl.W.map f) ↔ y ∈ J2Syl.U := fun y => by
    rw [Zc_map hf, J2Syl.Zc_W, Subgroup.mem_map_iff_mem hf]
  have key' : ∀ y : J2Syl, f y ∈ J2Syl.W.map f ↔ y ∈ J2Syl.W := fun y =>
    Subgroup.mem_map_iff_mem hf
  rcases sq_mem_R m with ⟨h1, h2⟩ | h1
  · left
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← map_mul, h1, map_one]
    · rcases h2 with h2 | h2
      · left; rw [← map_mul, key]; exact h2
      · right; rw [← map_mul, key']; exact h2
  · right
    rw [← map_mul, ← map_mul, h1]

theorem gen_Rp (h : J2Emb S T x) {z : G} (hz : IsZGen S z) : ∀ r ∈ S, r * r = z →
    ∃ s ∈ S, s * s = 1 ∧ s ≠ 1 ∧ s ≠ z ∧ (s ∈ Zc T ∨ s ∉ T) ∧ (s⁻¹ * r) * (s⁻¹ * r) = 1 ∧
      s⁻¹ * r ≠ 1 ∧ s⁻¹ * r ≠ z ∧ (s⁻¹ * r ∈ Zc T ∨ s⁻¹ * r ∉ T) := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  obtain rfl := hz.unique (isZGen_f hf)
  rintro _ ⟨m, rfl⟩ hm
  have hm' : m * m = J2Syl.z0 := hf (by rw [map_mul, hm])
  obtain ⟨s, h1, h2, h3, h4, h5, h6, h7, h8⟩ := gen_R m hm'
  have key : ∀ y : J2Syl, f y ∈ Zc (J2Syl.W.map f) ↔ y ∈ J2Syl.U := fun y => by
    rw [Zc_map hf, J2Syl.Zc_W, Subgroup.mem_map_iff_mem hf]
  have key' : ∀ y : J2Syl, f y ∈ J2Syl.W.map f ↔ y ∈ J2Syl.W := fun y =>
    Subgroup.mem_map_iff_mem hf
  refine ⟨f s, ⟨s, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h1, map_one]
  · intro h; exact h2 (hf (by rw [h, map_one]))
  · intro h; exact h3 (hf h)
  · rcases h4 with h4 | h4
    · left; rw [key]; exact h4
    · right; rw [key']; exact h4
  · rw [← map_inv, ← map_mul, ← map_mul, h5, map_one]
  · intro h; apply h6; apply hf; rw [map_mul, map_inv, map_one]; exact h
  · intro h; apply h7; apply hf; rw [map_mul, map_inv]; exact h
  · rcases h8 with h8 | h8
    · left; rw [← map_inv, ← map_mul, key]; exact h8
    · right; rw [← map_inv, ← map_mul, key']; exact h8

theorem faithful_Rp (h : J2Emb S T x) {z : G} (hz : IsZGen S z) : ∀ s ∈ S,
    (∀ r ∈ S, (((r * r = 1 ∧ (r ∈ Zc T ∨ r ∉ T)) ∨ r * r = z) →
      (s * r * s⁻¹ * r⁻¹ = 1 ∨ s * r * s⁻¹ * r⁻¹ = z))) →
    ((s * s = 1 ∧ (s ∈ Zc T ∨ s ∉ T)) ∨ s * s = z) := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  obtain rfl := hz.unique (isZGen_f hf)
  rintro _ ⟨m, rfl⟩ hc
  have key : ∀ y : J2Syl, f y ∈ Zc (J2Syl.W.map f) ↔ y ∈ J2Syl.U := fun y => by
    rw [Zc_map hf, J2Syl.Zc_W, Subgroup.mem_map_iff_mem hf]
  have key' : ∀ y : J2Syl, f y ∈ J2Syl.W.map f ↔ y ∈ J2Syl.W := fun y =>
    Subgroup.mem_map_iff_mem hf
  have hm := faithful_R m (fun r hr => by
    have := hc (f r) ⟨r, rfl⟩ (by
      rcases hr with ⟨h1, h2⟩ | h1
      · left
        refine ⟨?_, ?_⟩
        · rw [← map_mul, h1, map_one]
        · rcases h2 with h2 | h2
          · left; rw [key]; exact h2
          · right; rw [key']; exact h2
      · right; rw [← map_mul, h1])
    rcases this with h3 | h3
    · left; apply hf; simp only [map_mul, map_inv, map_one]; exact h3
    · right; apply hf; simp only [map_mul, map_inv]; exact h3)
  rcases hm with ⟨h1, h2⟩ | h1
  · left
    refine ⟨?_, ?_⟩
    · rw [← map_mul, h1, map_one]
    · rcases h2 with h2 | h2
      · left; rw [key]; exact h2
      · right; rw [key']; exact h2
  · right
    rw [← map_mul, h1]

end Transport

end CFSG.GH74.Uniqueness.SU.SU7.Model
