module

public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {M : Type*} [Group M]

@[expose] def adjoinL (g : M) (T : List M) : List M :=
  T ++ T.map (g * ·)

theorem mem_adjoinL {g x : M} {T : List M} : x ∈ adjoinL g T ↔ x ∈ T ∨ ∃ y ∈ T, x = g * y := by
  simp only [adjoinL, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, rfl⟩
  · rintro (h | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, rfl⟩

theorem length_adjoinL (g : M) (T : List M) : (adjoinL g T).length = 2 * T.length := by
  simp [adjoinL]
  omega

structure IsListSubgroupIn (S : Subgroup M) (T : List M) : Prop where
  nodup : T.Nodup
  subset : ∀ x ∈ T, x ∈ S
  one_mem : (1 : M) ∈ T
  mul_mem : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ T

theorem isListSubgroupIn_one (S : Subgroup M) : IsListSubgroupIn S [(1 : M)] where
  nodup := List.nodup_singleton _
  subset := by
    intro x hx
    rw [List.mem_singleton.1 hx]
    exact S.one_mem
  one_mem := List.mem_singleton_self _
  mul_mem := by
    intro x hx y hy
    rw [List.mem_singleton.1 hx, List.mem_singleton.1 hy, mul_one]
    exact List.mem_singleton_self _

theorem IsListSubgroupIn.adjoinL {S : Subgroup M} {T : List M} (hT : IsListSubgroupIn S T)
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1) {g : M} (hg : g ∈ S)
    (hgT : g ∉ T) : IsListSubgroupIn S (adjoinL g T) where
  nodup := by
    unfold CFSG.OddStandard.SmallF3.Omega.adjoinL
    rw [List.nodup_append]
    refine ⟨hT.nodup, hT.nodup.map (mul_right_injective g), ?_⟩
    intro x hx y hy hxy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    subst hxy
    apply hgT
    have h1 : g * z * z = g := by rw [mul_assoc, hsq z (hT.subset z hz), mul_one]
    rw [← h1]
    exact hT.mul_mem _ hx z hz
  subset := by
    intro x hx
    rcases mem_adjoinL.1 hx with h | ⟨y, hy, rfl⟩
    · exact hT.subset x h
    · exact S.mul_mem hg (hT.subset y hy)
  one_mem := mem_adjoinL.2 (Or.inl hT.one_mem)
  mul_mem := by
    intro x hx y hy
    rcases mem_adjoinL.1 hx with hx | ⟨x', hx', rfl⟩ <;>
      rcases mem_adjoinL.1 hy with hy | ⟨y', hy', rfl⟩
    · exact mem_adjoinL.2 (Or.inl (hT.mul_mem x hx y hy))
    · refine mem_adjoinL.2 (Or.inr ⟨x * y', hT.mul_mem x hx y' hy', ?_⟩)
      rw [← mul_assoc, ← mul_assoc, hc x (hT.subset x hx) g hg]
    · refine mem_adjoinL.2 (Or.inr ⟨x' * y, hT.mul_mem x' hx' y hy, ?_⟩)
      rw [mul_assoc]
    · refine mem_adjoinL.2 (Or.inl ?_)
      have h1 : g * x' * (g * y') = x' * y' := by
        calc g * x' * (g * y') = g * (x' * g) * y' := by group
          _ = g * (g * x') * y' := by rw [hc x' (hT.subset x' hx') g hg]
          _ = (g * g) * (x' * y') := by group
          _ = x' * y' := by rw [hsq g hg, one_mul]
      rw [h1]
      exact hT.mul_mem x' hx' y' hy'

theorem IsListSubgroupIn.exists_not_mem {S : Subgroup M} {T : List M} (hT : IsListSubgroupIn S T)
    (hlt : T.length < Nat.card S) : ∃ g ∈ S, g ∉ T := by
  classical
  by_contra h
  push Not at h
  have hsub : (S : Set M) ⊆ ↑T.toFinset := fun x hx => by
    simpa using h x hx
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hT.nodup] at h1
  have h2 : Nat.card S = (S : Set M).ncard := Nat.card_coe_set_eq (S : Set M)
  omega

theorem IsListSubgroupIn.mem_of_length_eq {S : Subgroup M} {T : List M}
    (hT : IsListSubgroupIn S T) (hlen : T.length = Nat.card S) {x : M} (hx : x ∈ S) : x ∈ T := by
  classical
  by_contra hxT
  haveI : Finite S :=
    Nat.finite_of_card_ne_zero (by rw [← hlen]; exact (List.length_pos_of_mem hT.one_mem).ne')
  have hsub : (↑(insert x T.toFinset) : Set M) ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with rfl | hy
    · exact hx
    · exact hT.subset y (List.mem_toFinset.1 hy)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simpa using hxT),
    List.toFinset_card_of_nodup hT.nodup] at h1
  have h2 : Nat.card S = (S : Set M).ncard := Nat.card_coe_set_eq (S : Set M)
  omega

theorem exists_basis_four (S : Subgroup M) (hcard : Nat.card S = 16)
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1) {a : M} (ha : a ∈ S)
    (ha1 : a ≠ 1) :
    ∃ b c d : M, b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ b ∉ adjoinL a [1] ∧ c ∉ adjoinL b (adjoinL a [1]) ∧
      d ∉ adjoinL c (adjoinL b (adjoinL a [1])) ∧
      ∀ x, x ∈ S ↔ x ∈ adjoinL d (adjoinL c (adjoinL b (adjoinL a [1]))) := by
  have h0 := isListSubgroupIn_one S
  have ha' : a ∉ [(1 : M)] := by simpa using ha1
  have h1 := h0.adjoinL hc hsq ha ha'
  have l1 : (adjoinL a [1]).length = 2 := by rw [length_adjoinL]; rfl
  obtain ⟨b, hb, hbT⟩ := h1.exists_not_mem (by rw [l1, hcard]; norm_num)
  have h2 := h1.adjoinL hc hsq hb hbT
  have l2 : (adjoinL b (adjoinL a [1])).length = 4 := by rw [length_adjoinL, l1]
  obtain ⟨c, hc', hcT⟩ := h2.exists_not_mem (by rw [l2, hcard]; norm_num)
  have h3 := h2.adjoinL hc hsq hc' hcT
  have l3 : (adjoinL c (adjoinL b (adjoinL a [1]))).length = 8 := by rw [length_adjoinL, l2]
  obtain ⟨d, hd, hdT⟩ := h3.exists_not_mem (by rw [l3, hcard]; norm_num)
  have h4 := h3.adjoinL hc hsq hd hdT
  have l4 : (adjoinL d (adjoinL c (adjoinL b (adjoinL a [1])))).length = Nat.card S := by
    rw [length_adjoinL, l3, hcard]
  exact ⟨b, c, d, hb, hc', hd, hbT, hcT, hdT, fun x =>
    ⟨fun hx => h4.mem_of_length_eq l4 hx, fun hx => h4.subset x hx⟩⟩

theorem exists_basis_three (S : Subgroup M) (hcard : Nat.card S = 8)
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1) :
    ∃ a b c : M, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ 1 ∧ b ∉ adjoinL a [1] ∧
      c ∉ adjoinL b (adjoinL a [1]) ∧
      ∀ x, x ∈ S ↔ x ∈ adjoinL c (adjoinL b (adjoinL a [1])) := by
  have h0 := isListSubgroupIn_one S
  obtain ⟨a, ha, haT⟩ := h0.exists_not_mem (by rw [hcard]; norm_num [List.length_singleton])
  have ha1 : a ≠ 1 := by simpa using haT
  have h1 := h0.adjoinL hc hsq ha haT
  have l1 : (adjoinL a [1]).length = 2 := by rw [length_adjoinL]; rfl
  obtain ⟨b, hb, hbT⟩ := h1.exists_not_mem (by rw [l1, hcard]; norm_num)
  have h2 := h1.adjoinL hc hsq hb hbT
  have l2 : (adjoinL b (adjoinL a [1])).length = 4 := by rw [length_adjoinL, l1]
  obtain ⟨c, hc', hcT⟩ := h2.exists_not_mem (by rw [l2, hcard]; norm_num)
  have h3 := h2.adjoinL hc hsq hc' hcT
  have l3 : (adjoinL c (adjoinL b (adjoinL a [1]))).length = Nat.card S := by
    rw [length_adjoinL, l2, hcard]
  exact ⟨a, b, c, ha, hb, hc', ha1, hbT, hcT, fun x =>
    ⟨fun hx => h3.mem_of_length_eq l3 hx, fun hx => h3.subset x hx⟩⟩

end CFSG.OddStandard.SmallF3.Omega
