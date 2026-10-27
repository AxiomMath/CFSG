module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
private lemma card_orbit_mul_card_inf (K : Subgroup (Perm α)) (x : α) :
    Nat.card (orbit K x) * Nat.card ↥(K ⊓ stabilizer (Perm α) x) = Nat.card K := by
  rw [← Subgroup.index_mul_card (stabilizer K x), index_stabilizer, Nat.card_coe_set_eq]
  congr 1
  rw [← Subgroup.card_subtype K (stabilizer K x), ← stabilizer_subgroupOf,
    Subgroup.subgroupOf_map_subtype, inf_comm]

omit [DecidableEq α] in
theorem exists_block_of_isPGroup {P : Subgroup (Perm α)} (hP : IsPGroup 2 P) (x : α) {i j : ℕ}
    (hj : Nat.card (orbit P x) = 2 ^ j) (hij : i ≤ j) :
    ∃ B : Set α, x ∈ B ∧ B ⊆ orbit P x ∧ Nat.card B = 2 ^ i ∧
      ∀ g ∈ P, ∀ y ∈ B, g y ∈ B → ∀ z ∈ B, g z ∈ B := by
  have hA := card_orbit_mul_card_inf P x
  rw [hj] at hA
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (Dvd.intro_left (2 ^ j) (hA.trans ha) : Nat.card ↥(P ⊓ stabilizer (Perm α) x) ∣ 2 ^ a)
  have hmj : j + m = a := by
    apply Nat.pow_right_injective le_rfl
    show 2 ^ (j + m) = 2 ^ a
    rw [pow_add, ← hm, hA, ha]
  obtain ⟨K, hKc, hHK, hKP⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := m + i) (H := P ⊓ stabilizer (Perm α) x) (L := P)
    (hm ▸ pow_dvd_pow 2 (Nat.le_add_right m i)) (ha ▸ pow_dvd_pow 2 (by omega)) inf_le_left
  refine ⟨orbit K x, mem_orbit_self x, ?_, ?_, ?_⟩
  · rintro y ⟨k, rfl⟩
    exact ⟨⟨k, hKP k.2⟩, rfl⟩
  · have hK := card_orbit_mul_card_inf K x
    rw [show K ⊓ stabilizer (Perm α) x = P ⊓ stabilizer (Perm α) x from
      le_antisymm (inf_le_inf_right _ hKP) (le_inf hHK inf_le_right), hm, hKc, pow_add,
      mul_comm] at hK
    exact Nat.eq_of_mul_eq_mul_left (pow_pos two_pos m) hK
  · rintro g hg y ⟨k, rfl⟩ ⟨k', hk'⟩ z ⟨k'', rfl⟩
    have hmem : (k' : Perm α)⁻¹ * g * k ∈ P ⊓ stabilizer (Perm α) x := by
      refine Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem (P.inv_mem (hKP k'.2)) hg) (hKP k.2), ?_⟩
      have hk'' : (k' : Perm α) x = g ((k : Perm α) x) := hk'
      rw [mem_stabilizer_iff, Perm.smul_def, Perm.mul_apply, Perm.mul_apply, ← hk'']
      exact (k' : Perm α).symm_apply_apply x
    have hgK : g ∈ K := by
      simpa [mul_assoc] using K.mul_mem (K.mul_mem k'.2 (hHK hmem)) (K.inv_mem k.2)
    exact ⟨⟨g, hgK⟩ * k'', by simp [Subgroup.smul_def]⟩

private def BlockRel (P : Subgroup (Perm α)) (B : Set α) (y z : α) : Prop :=
  y = z ∨ ∃ g ∈ P, (g : Perm α)⁻¹ y ∈ B ∧ (g : Perm α)⁻¹ z ∈ B

omit [Fintype α] [DecidableEq α] in
private lemma blockRel_symm {P : Subgroup (Perm α)} {B : Set α} {y z : α}
    (h : BlockRel P B y z) : BlockRel P B z y :=
  h.imp Eq.symm fun ⟨g, hg, h₁, h₂⟩ => ⟨g, hg, h₂, h₁⟩

omit [Fintype α] [DecidableEq α] in
private lemma blockRel_trans {P : Subgroup (Perm α)} {B : Set α}
    (hB : ∀ g ∈ P, ∀ y ∈ B, g y ∈ B → ∀ z ∈ B, g z ∈ B) {y z w : α}
    (h₁ : BlockRel P B y z) (h₂ : BlockRel P B z w) : BlockRel P B y w := by
  rcases h₁ with rfl | ⟨g, hg, hyB, hzB⟩
  · exact h₂
  rcases h₂ with rfl | ⟨h, hh, hzB', hwB⟩
  · exact Or.inr ⟨g, hg, hyB, hzB⟩
  refine Or.inr ⟨g, hg, hyB, ?_⟩
  have key : (g⁻¹ * h : Perm α) (h⁻¹ z) ∈ B := by simpa using hzB
  simpa using hB (g⁻¹ * h) (P.mul_mem (P.inv_mem hg) hh) _ hzB' key _ hwB

omit [Fintype α] [DecidableEq α] in
private lemma blockRel_smul_iff {P : Subgroup (Perm α)} {B : Set α} {g : Perm α} (hg : g ∈ P)
    (y z : α) : BlockRel P B (g y) (g z) ↔ BlockRel P B y z := by
  have key : ∀ g : Perm α, g ∈ P → ∀ y z, BlockRel P B y z → BlockRel P B (g y) (g z) := by
    rintro g hg y z (rfl | ⟨h, hh, h₁, h₂⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨g * h, P.mul_mem hg hh, by simpa using h₁, by simpa using h₂⟩
  exact ⟨fun h => by simpa using key g⁻¹ (P.inv_mem hg) _ _ h, key g hg y z⟩

omit [Fintype α] [DecidableEq α] in
private lemma blockRel_mem_orbit {P : Subgroup (Perm α)} {B : Set α} {x : α}
    (hBO : B ⊆ orbit P x) {y z : α} (h : BlockRel P B y z) (hne : y ≠ z) :
    y ∈ orbit P x ∧ z ∈ orbit P x := by
  have key : ∀ (g : Perm α), g ∈ P → ∀ u ∈ orbit P x, g u ∈ orbit P x := by
    rintro g hg _ ⟨p, rfl⟩
    exact ⟨⟨g, hg⟩ * p, rfl⟩
  obtain h | ⟨g, hg, h₁, h₂⟩ := h
  · exact absurd h hne
  · exact ⟨by simpa using key g hg _ (hBO h₁), by simpa using key g hg _ (hBO h₂)⟩

omit [Fintype α] [DecidableEq α] in
private lemma card_blockRel {P : Subgroup (Perm α)} {B : Set α} {x : α} (hxB : x ∈ B)
    (hB : ∀ g ∈ P, ∀ y ∈ B, g y ∈ B → ∀ z ∈ B, g z ∈ B) {g : Perm α} (hg : g ∈ P) :
    Nat.card {z // BlockRel P B (g x) z} = Nat.card B := by
  have hiff : ∀ z, BlockRel P B (g x) z ↔ g⁻¹ z ∈ B := by
    intro z
    refine ⟨?_, fun hz => Or.inr ⟨g, hg, by simpa using hxB, hz⟩⟩
    rintro (rfl | ⟨h, hh, h₁, h₂⟩)
    · simpa using hxB
    · have key : (g⁻¹ * h : Perm α) (h⁻¹ (g x)) ∈ B := by simpa using hxB
      simpa using hB (g⁻¹ * h) (P.mul_mem (P.inv_mem hg) hh) _ h₁ key _ h₂
  exact Nat.card_congr
    ((Equiv.subtypeEquivRight hiff).trans (Equiv.subtypeEquiv (g⁻¹ : Perm α) fun z => Iff.rfl))

omit [Fintype α] [DecidableEq α] in
theorem exists_setoid_of_block {P : Subgroup (Perm α)} {x : α} {B : Set α} (hxB : x ∈ B)
    (hBO : B ⊆ orbit P x) (hB : ∀ g ∈ P, ∀ y ∈ B, g y ∈ B → ∀ z ∈ B, g z ∈ B) :
    ∃ t : Setoid α, (∀ g ∈ P, ∀ y z, t.r (g y) (g z) ↔ t.r y z) ∧
      (∀ y z, t.r y z → (y ∈ orbit P x ↔ z ∈ orbit P x)) ∧
      (∀ y, y ∉ orbit P x → ∀ z, t.r y z → z = y) ∧
      (∀ y ∈ orbit P x, Nat.card {z // t.r y z} = Nat.card B) ∧
      (∀ y z, t.r y z ↔ y = z ∨ ∃ g ∈ P, (g : Perm α)⁻¹ y ∈ B ∧ (g : Perm α)⁻¹ z ∈ B) := by
  refine ⟨⟨BlockRel P B, ⟨fun _ => Or.inl rfl, blockRel_symm, blockRel_trans hB⟩⟩, ?_, ?_, ?_, ?_,
    fun y z => Iff.rfl⟩
  · exact fun g hg y z => blockRel_smul_iff hg y z
  · intro y z h
    by_cases hyz : y = z
    · rw [hyz]
    · obtain ⟨h₁, h₂⟩ := blockRel_mem_orbit hBO h hyz
      exact ⟨fun _ => h₂, fun _ => h₁⟩
  · intro y hy z h
    by_contra hne
    exact hy (blockRel_mem_orbit hBO h (Ne.symm hne)).1
  · rintro y ⟨⟨g, hg⟩, rfl⟩
    exact card_blockRel hxB hB hg

end CFSG.GroupTheory.AltCore
