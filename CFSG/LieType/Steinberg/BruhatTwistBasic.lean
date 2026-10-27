module

public import CFSG.LieType.Steinberg.Collection
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

section Commutator

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left (x₁ x₂ y : G) :
    ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right (x y₁ y₂ : G) :
    ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mem_of_mem_iSup {ι κ : Sort*} {A : ι → Subgroup G}
    {B : κ → Subgroup G} {N : Subgroup G} (hA : ∀ i, A i ≤ Subgroup.normalizer (N : Set G))
    (hB : ∀ j, B j ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ i j, ∀ a ∈ A i, ∀ b ∈ B j, ⁅a, b⁆ ∈ N) {x y : G} (hx : x ∈ ⨆ i, A i)
    (hy : y ∈ ⨆ j, B j) : ⁅x, y⁆ ∈ N := by
  have hA' : ⨆ i, A i ≤ Subgroup.normalizer (N : Set G) := iSup_le hA
  have hB' : ⨆ j, B j ≤ Subgroup.normalizer (N : Set G) := iSup_le hB
  have hconj : ∀ {z : G}, z ∈ Subgroup.normalizer (N : Set G) → ∀ {m : G}, m ∈ N →
      z * m * z⁻¹ ∈ N := fun hz m hm => (Subgroup.mem_normalizer_iff.1 hz m).1 hm
  have step : ∀ j, ∀ b ∈ B j, ⁅x, b⁆ ∈ N := by
    intro j b hb
    refine Subgroup.iSup_induction' A (C := fun x _ => ⁅x, b⁆ ∈ N)
      (fun i a ha => h i j a ha b hb) ?_ (fun x₁ x₂ hx₁ _ h₁ h₂ => ?_) hx
    · show ⁅(1 : G), b⁆ ∈ N
      rw [show ⁅(1 : G), b⁆ = 1 by rw [commutatorElement_def]; group]
      exact one_mem N
    rw [commutatorElement_mul_left]
    exact mul_mem (hconj (hA' hx₁) h₂) h₁
  refine Subgroup.iSup_induction' B (C := fun y _ => ⁅x, y⁆ ∈ N) (fun j b hb => step j b hb)
    ?_ (fun y₁ y₂ hy₁ _ h₁ h₂ => ?_) hy
  · show ⁅x, (1 : G)⁆ ∈ N
    rw [show ⁅x, (1 : G)⁆ = 1 by rw [commutatorElement_def]; group]
    exact one_mem N
  rw [commutatorElement_mul_right]
  exact mul_mem h₁ (hconj (hB' hy₁) h₂)

theorem iSup_subgroupOf {ι : Sort*} {F : Subgroup G} {T : ι → Subgroup G} (hT : ∀ i, T i ≤ F) :
    (⨆ i, T i).subgroupOf F = ⨆ i, (T i).subgroupOf F := by
  apply Subgroup.map_injective F.subtype_injective
  rw [Subgroup.map_iSup, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (iSup_le hT)]
  exact iSup_congr fun i => by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hT i)]

end Commutator

section Blocks

variable {V : Type*} [DecidableEq V] (ρ : V → V)

@[expose] def pairBlock (m : V) : List V := if ρ m = m then [m] else [m, ρ m]

variable {ρ}

theorem mem_pairBlock {m x : V} : x ∈ pairBlock ρ m ↔ x = m ∨ x = ρ m := by
  unfold pairBlock
  split_ifs with h
  · simp only [List.mem_singleton]
    exact ⟨Or.inl, fun h' => h'.elim id fun h'' => h'' ▸ h⟩
  · simp

theorem nodup_pairBlock (m : V) : (pairBlock ρ m).Nodup := by
  unfold pairBlock
  split_ifs with h
  · exact List.nodup_singleton m
  · simp [Ne.symm h]

theorem prod_map_pairBlock_comp {M : Type*} [Monoid M] (F : V → M) {m : V}
    (hρ : ρ (ρ m) = m) (h : ρ m ≠ m → Commute (F m) (F (ρ m))) :
    ((pairBlock ρ m).map (F ∘ ρ)).prod = ((pairBlock ρ m).map F).prod := by
  unfold pairBlock
  split_ifs with h'
  · simp [h']
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Function.comp_apply, hρ]
    exact (h h').symm.eq

omit [DecidableEq V] in
theorem prod_map_flatMap {M : Type*} [Monoid M] (φ : V → M) (f : V → List V) (l : List V) :
    ((l.flatMap f).map φ).prod = (l.map fun m => ((f m).map φ).prod).prod := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_cons, List.prod_cons]

theorem exists_nodup_sorted {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℤ) :
    ∃ L : List α, L.Nodup ∧ (∀ a, a ∈ L ↔ a ∈ s) ∧ L.Pairwise (fun a b => f a ≤ f b) := by
  refine ⟨hs.toFinset.toList.mergeSort (fun a b => decide (f a ≤ f b)), ?_, fun a => ?_, ?_⟩
  · exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  · rw [(List.mergeSort_perm _ _).mem_iff, Finset.mem_toList, hs.mem_toFinset]
  · refine (List.pairwise_mergeSort (fun a b c hab hbc => ?_) (fun a b => ?_) _).imp ?_
    · simp only [decide_eq_true_eq] at hab hbc ⊢
      exact hab.trans hbc
    · simpa using le_total (f a) (f b)
    · intro a b h
      simpa using h

theorem exists_list_flatMap_pairBlock {β : Type*} [LinearOrder β] {ord : V → β}
    (hord : Function.Injective ord) (hρ : ∀ v, ρ (ρ v) = v) (key : V → ℤ)
    (hkey : ∀ v, key (ρ v) = key v) {S : Set V} (hS : S.Finite) (hSρ : ∀ v ∈ S, ρ v ∈ S) :
    ∃ M : List V, (∀ m ∈ M, m ∈ S) ∧ (∀ v, v ∈ M.flatMap (pairBlock ρ) ↔ v ∈ S) ∧
      (M.flatMap (pairBlock ρ)).Nodup ∧
        (M.flatMap (pairBlock ρ)).Pairwise (fun a b => key a ≤ key b) := by
  set R : Set V := {v | v ∈ S ∧ ord v ≤ ord (ρ v)}
  have hRS : ∀ v ∈ R, v ∈ S := fun v hv => hv.1
  have hR : ∀ m ∈ R, ∀ m' ∈ R, m' = ρ m → m' = m := by
    rintro m ⟨-, hm⟩ m' ⟨-, hm'⟩ rfl
    rw [hρ] at hm'
    exact hord (le_antisymm hm' hm)
  obtain ⟨M, hnd, hmem, hsort⟩ := exists_nodup_sorted (hS.subset hRS) key
  refine ⟨M, fun m hm => ((hmem m).1 hm).1, fun v => ?_, ?_, ?_⟩
  · rw [List.mem_flatMap]
    constructor
    · rintro ⟨m, hm, hv⟩
      rcases mem_pairBlock.1 hv with rfl | rfl
      · exact ((hmem _).1 hm).1
      · exact hSρ m ((hmem m).1 hm).1
    · intro hv
      rcases le_total (ord v) (ord (ρ v)) with h | h
      · exact ⟨v, (hmem v).2 ⟨hv, h⟩, mem_pairBlock.2 (Or.inl rfl)⟩
      · refine ⟨ρ v, (hmem _).2 ⟨hSρ v hv, by rwa [hρ]⟩, mem_pairBlock.2 (Or.inr (hρ v).symm)⟩
  · refine List.nodup_flatMap.2 ⟨fun m _ => nodup_pairBlock m, ?_⟩
    refine hnd.imp_of_mem fun {m m'} hm hm' hne => ?_
    have hmR := (hmem m).1 hm
    have hm'R := (hmem m').1 hm'
    refine List.disjoint_left.2 fun {x} hx hx' => hne ?_
    rcases mem_pairBlock.1 hx with h₁ | h₁ <;> rcases mem_pairBlock.1 hx' with h₂ | h₂
    · exact h₁.symm.trans h₂
    · exact hR m' hm'R m hmR (by rw [← h₁]; exact h₂)
    · exact (hR m hmR m' hm'R (by rw [← h₂]; exact h₁)).symm
    · calc m = ρ (ρ m) := (hρ m).symm
        _ = ρ (ρ m') := by rw [← h₁, h₂]
        _ = m' := hρ m'
  · refine List.pairwise_flatMap.2 ⟨fun m _ => ?_, hsort.imp fun {m m'} h x hx y hy => ?_⟩
    · unfold pairBlock
      split_ifs
      · exact List.pairwise_singleton _ _
      · simp [hkey]
    · rcases mem_pairBlock.1 hx with rfl | rfl <;> rcases mem_pairBlock.1 hy with rfl | rfl <;>
        simpa [hkey] using h

end Blocks

end CFSG.LieType.Steinberg
