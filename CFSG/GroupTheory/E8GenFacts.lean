module

public import Mathlib.GroupTheory.Sylow

import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.GroupTheory

open scoped Pointwise

@[expose] def E8Facts (G : Type*) [Group G] (A : Subgroup G) : Prop :=
  Nat.card A = 8 ∧
    (⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set G)) = ⊤ ∧
    Subgroup.normalClosure (A : Set G) = ⊤ ∧
    ∀ a ∈ A, a ≠ 1 → 3 ∣ Nat.card (Subgroup.centralizer ({a} : Set G))

@[expose] def E8GenFacts (G : Type*) [Group G] : Prop :=
  ∀ A : Subgroup G, (∀ a ∈ A, a ^ 2 = 1) → 8 ≤ Nat.card A → E8Facts G A

theorem E8Facts.of_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {A : Subgroup G}
    (h : E8Facts H (A.map e.toMonoidHom)) : E8Facts G A := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hcard : Nat.card A = 8 := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact h1
  refine ⟨hcard, ?_, ?_, ?_⟩
  · have hbij : Set.BijOn (e : G → H) (A : Set G) (A.map e.toMonoidHom : Set H) := by
      refine ⟨fun x hx => Subgroup.mem_map_of_mem e.toMonoidHom hx, ?_, ?_⟩
      · intro x _ y _ hxy
        exact e.injective hxy
      · intro y hy
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
        exact ⟨x, hx, hxy⟩
    have hsup : (⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({e a} : Set H)) =
        ⨆ b ∈ (A.map e.toMonoidHom : Subgroup H), ⨆ (_ : b ≠ 1),
          Subgroup.centralizer ({b} : Set H) := by
      simpa using Set.BijOn.iSup_comp
        (fun b : H => ⨆ (_ : b ≠ 1), Subgroup.centralizer ({b} : Set H)) hbij
    have hmap : (⨆ a ∈ A, ⨆ (_ : a ≠ 1),
        Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom = ⊤ := by
      simp_rw [Subgroup.map_iSup]
      simp only [CFSG.centralizer_singleton_map e]
      rw [hsup, h2]
    rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom)
      (H := ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set G)) e.injective]
    rw [hmap, Subgroup.comap_top]
  · rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom)
      (H := Subgroup.normalClosure (A : Set G)) e.injective]
    rw [Subgroup.map_normalClosure _ _ e.surjective, ← Subgroup.coe_map, h3,
      Subgroup.comap_top]
  · intro a ha ha1
    have h4a := h4 (e a) (Subgroup.mem_map_of_mem e.toMonoidHom ha)
      (fun h => ha1 (e.injective (by simpa using h)))
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom)
        (K := Subgroup.centralizer ({a} : Set G)) e.injective,
      CFSG.centralizer_singleton_map e a]
    exact h4a

theorem E8GenFacts.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : E8GenFacts H) : E8GenFacts G := by
  intro A hA2 hA8
  refine E8Facts.of_map e (h (A.map e.toMonoidHom) ?_ ?_)
  · rintro b ⟨a, ha, rfl⟩
    simpa using congrArg (e : G →* H) (hA2 a ha)
  · rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hA8

theorem E8GenFacts.of_sylow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : ∀ A : Subgroup G, A ≤ S → (∀ a ∈ A, a ^ 2 = 1) → 8 ≤ Nat.card A → E8Facts G A) :
    E8GenFacts G := by
  intro A hA2 hA8
  have hApg : IsPGroup 2 A := fun a => ⟨1, by
    apply Subtype.ext
    simpa using hA2 (a : G) a.2⟩
  obtain ⟨T, hAT⟩ := hApg.exists_le_sylow
  have hpre : MulAction.IsPretransitive G (Sylow 2 G) :=
    @Sylow.isPretransitive_of_finite 2 G _ ⟨Nat.prime_two⟩ (Sylow.finite_of_finiteIndex T)
  obtain ⟨g, hg⟩ := hpre.exists_smul_eq T S
  have hS : (S : Subgroup G) = T.toSubgroup.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hA'S : A.map (MulAut.conj g).toMonoidHom ≤ S := by
    rw [hS]
    exact Subgroup.map_mono hAT
  have hA'2 : ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, a ^ 2 = 1 := by
    rintro x ⟨a, ha, rfl⟩
    simpa using congrArg (MulAut.conj g) (hA2 a ha)
  have hA'8 : 8 ≤ Nat.card (A.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    exact hA8
  exact E8Facts.of_map (MulAut.conj g) (h _ hA'S hA'2 hA'8)

end CFSG.GroupTheory
