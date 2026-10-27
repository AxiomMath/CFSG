module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KSeitz

@[expose] def hset (f : ℕ) {G : Type*} [Group G] (E : Subgroup G) : Set G :=
  {k | ∃ F : Subgroup G, F ≤ E ∧ F.relIndex E = f ∧ ∀ y ∈ F, y * k = k * y}

theorem hset_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (f : ℕ) (E : Subgroup G) :
    hset f (E.map e.toMonoidHom) = e '' hset f E := by
  ext k
  constructor
  · rintro ⟨F, hFE, hrel, hcomm⟩
    refine ⟨e.symm k, ⟨F.comap e.toMonoidHom, ?_, ?_, ?_⟩, by simp⟩
    · intro y hy
      have h1 : e y ∈ E.map e.toMonoidHom := hFE hy
      obtain ⟨z, hz, hzy⟩ := h1
      have : z = y := e.injective hzy
      exact this ▸ hz
    · rw [Subgroup.relIndex_comap]
      exact hrel
    · intro y hy
      have h1 : e y * k = k * e y := hcomm (e y) hy
      apply e.injective
      rw [map_mul, map_mul]
      simpa using h1
  · rintro ⟨k₀, ⟨F, hFE, hrel, hcomm⟩, rfl⟩
    refine ⟨F.map e.toMonoidHom, Subgroup.map_mono hFE, ?_, ?_⟩
    · rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]
      exact hrel
    · rintro _ ⟨y, hy, rfl⟩
      have h1 := hcomm y hy
      show e y * e k₀ = e k₀ * e y
      rw [← map_mul, ← map_mul, h1]

theorem closure_hset_map_eq_top_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) (f : ℕ)
    (E : Subgroup G) :
    Subgroup.closure (hset f (E.map e.toMonoidHom)) = ⊤ ↔ Subgroup.closure (hset f E) = ⊤ := by
  have hc : Subgroup.closure (e '' hset f E) = (Subgroup.closure (hset f E)).map e.toMonoidHom :=
    (MonoidHom.map_closure e.toMonoidHom _).symm
  rw [hset_map, hc]
  constructor
  · intro h
    have h' := congrArg (Subgroup.map e.symm.toMonoidHom) h
    rw [Subgroup.map_map] at h'
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [hid, Subgroup.map_id, Subgroup.map_top_of_surjective _ e.symm.surjective] at h'
    exact h'
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ e.surjective

theorem mem_hset {G : Type*} [Group G] {f : ℕ} {E F : Subgroup G} (hFE : F ≤ E)
    (hrel : F.relIndex E = f) {k : G} (hk : ∀ y ∈ F, y * k = k * y) : k ∈ hset f E :=
  ⟨F, hFE, hrel, hk⟩

end KSeitz

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
