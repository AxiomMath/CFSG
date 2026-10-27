module

public import CFSG.GH74.Uniqueness.SU.SU5J2Emb2
public import CFSG.GH74.Uniqueness.SU.SU5J2U

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace J2Syl

theorem sq_mem_centralizer : ∀ s m : J2Syl, s.right ≠ 1 → s * s = 1 → m * s = s * m →
    (m * m = 1 ∨ m * m = z0) := by decide +kernel

theorem exists_sq_eq_z (s : J2Syl) (hs : s.right ≠ 1) (hs2 : s * s = 1) (M : Subgroup J2Syl)
    (hM : ∀ m ∈ M, m * s = s * m) (hcard : 5 ≤ Nat.card M) : ∃ m ∈ M, m * m = z0 := by
  by_contra hcon
  have hcon' : ∀ m ∈ M, m * m ≠ z0 := fun m hm h => hcon ⟨m, hm, h⟩
  have hsub : ∀ t ∈ M, t ∈ ({1, s, z0, s * z0} : Finset J2Syl) := by
    intro t ht
    have h2 : t * t = 1 := (sq_mem_centralizer s t hs hs2 (hM t ht)).resolve_right (hcon' t ht)
    have := cert_cent s t hs hs2 (hM t ht) h2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h4 : Nat.card M ≤ 4 := (card_le_card_of_subset_finset hsub).trans Finset.card_le_four
  omega

theorem cent_U : ∀ u g : J2Syl, u ∈ U → u ≠ 1 → u ≠ z0 → (g * u = u * g ↔ g ∈ W) := by
  decide +kernel

theorem ncard_setOf_eq_card_filter {M : Type*} [Fintype M] (p : M → Prop) [DecidablePred p] :
    {s : M | p s}.ncard = (Finset.univ.filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext s
  simp

theorem ncard_invol_not_W : {s : J2Syl | s ∉ W ∧ s * s = 1}.ncard = 8 := by
  rw [ncard_setOf_eq_card_filter]
  exact card_invol_not_W

end J2Syl

section Emb4

variable {G : Type*} [Group G]

namespace J2Emb

variable {S T : Subgroup G} {x : G}

theorem exists_sq_eq_z (h : J2Emb S T x) {z : G} (hz : IsZGen S z) :
    ∀ s ∈ S, s ∉ T → s ^ 2 = 1 → ∀ M : Subgroup G, M ≤ S ⊓ centralizer {s} → 5 ≤ Nat.card M →
      ∃ m ∈ M, m ^ 2 = z := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  obtain rfl := hz.unique (isZGen_f hf)
  rintro _ ⟨s, rfl⟩ hsT hs2 M hM hcard
  have h1 : s.right ≠ 1 := fun h0 => hsT (Subgroup.mem_map_of_mem f h0)
  have h2 : s * s = 1 := hf (by rw [map_mul, map_one, ← pow_two]; exact hs2)
  obtain ⟨M₀, rfl⟩ := exists_eq_map_of_le_range (hM.trans inf_le_left)
  rw [Subgroup.card_map_of_injective hf] at hcard
  have hM₀ : ∀ m ∈ M₀, m * s = s * m := by
    intro m hm
    have h3 := Subgroup.mem_centralizer_iff.1 (hM (Subgroup.mem_map_of_mem f hm)).2 (f s) rfl
    exact hf (by rw [map_mul, map_mul]; exact h3.symm)
  obtain ⟨m, hm, hmz⟩ := J2Syl.exists_sq_eq_z s h1 h2 M₀ hM₀ hcard
  exact ⟨f m, Subgroup.mem_map_of_mem f hm, by rw [pow_two, ← map_mul, hmz]⟩

theorem half_central (h : J2Emb S T x) {z : G} (hz : IsZGen S z) :
    ∀ u ∈ Zc T, u ≠ 1 → u ≠ z → ∀ g ∈ S, (g * u = u * g ↔ g ∈ T) := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  obtain rfl := hz.unique (isZGen_f hf)
  rintro u hu hu1 huz _ ⟨g, rfl⟩
  rw [Zc_map hf, J2Syl.Zc_W] at hu
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hu
  have hm1 : m ≠ 1 := fun h0 => hu1 (by rw [h0, map_one])
  have hmz : m ≠ J2Syl.z0 := fun h0 => huz (by rw [h0])
  rw [← map_mul, ← map_mul, hf.eq_iff, Subgroup.mem_map_iff_mem hf]
  exact J2Syl.cent_U m g hm hm1 hmz

theorem card_invol (h : J2Emb S T x) : {s : G | s ∈ S ∧ s ∉ T ∧ s ^ 2 = 1}.ncard = 8 := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  have hset : {s : G | s ∈ f.range ∧ s ∉ J2Syl.W.map f ∧ s ^ 2 = 1} =
      f '' {s : J2Syl | s ∉ J2Syl.W ∧ s * s = 1} := by
    ext g
    constructor
    · rintro ⟨⟨m, rfl⟩, hmT, hm2⟩
      refine ⟨m, ⟨fun h0 => hmT (Subgroup.mem_map_of_mem f h0), ?_⟩, rfl⟩
      exact hf (by rw [map_mul, map_one, ← pow_two]; exact hm2)
    · rintro ⟨m, hm, rfl⟩
      refine ⟨⟨m, rfl⟩, fun h0 => hm.1 ((Subgroup.mem_map_iff_mem hf).1 h0), ?_⟩
      rw [pow_two, ← map_mul, hm.2, map_one]
  rw [hset, Set.ncard_image_of_injective _ hf, J2Syl.ncard_invol_not_W]

end J2Emb

end Emb4

end CFSG.GH74.Uniqueness.SU.SU5
