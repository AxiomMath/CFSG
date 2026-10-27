module

public import CFSG.GH74.KGroups.Generic6
public import CFSG.GroupTheory.E8GenFacts

public section

namespace CFSG.GH74.KGroups

open CFSG.GroupTheory

theorem AutModel.conj_mem {K G : Type*} [Group K] [Group G] (M : AutModel K G) {g x : G}
    (hg : g ∈ M.A) (hx : x ∈ M.P) : g * x * g⁻¹ ∈ M.P := by
  obtain ⟨φ, hφ⟩ := M.Φ.surjective ⟨g, hg⟩
  obtain ⟨k, hk⟩ := M.e.surjective ⟨x, hx⟩
  have hg' : (M.Φ φ : G) = g := congrArg Subtype.val hφ
  have hk' : ((M.e k : M.P) : G) = x := congrArg Subtype.val hk
  rw [← hg', ← hk', ← M.spec φ k]
  exact (M.e (φ k)).2

theorem AutModel.nonempty_mulEquiv_or_eq_top {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hN : Subgroup.centralizer (N : Set H) = ⊥) {G : Type*} [Group G]
    (M : AutModel N G) (h2 : Nat.card M.A = 2 * Nat.card M.P) :
    Nonempty (H ≃* M.A) ∨ N = ⊤ := by
  classical
  let f : H →* ↥M.A := (M.actHom N).codRestrict M.A (M.actHom_mem N)
  have hf : Function.Injective f := fun a b hab =>
    M.actHom_injective N hN (congrArg Subtype.val hab)
  have hPpos : 0 < Nat.card ↥M.P := by
    rw [← Nat.card_congr M.e.toEquiv]
    exact Nat.card_pos_iff.2 ⟨⟨1, N.one_mem⟩, inferInstance⟩
  have hNpos : 0 < Nat.card ↥N := Nat.card_pos_iff.2 ⟨⟨1, N.one_mem⟩, inferInstance⟩
  have hHpos : 0 < Nat.card H := Nat.card_pos_iff.2 ⟨⟨1⟩, inferInstance⟩
  have hAfin : Finite ↥M.A := by
    apply Nat.finite_of_card_ne_zero
    rw [h2]
    exact Nat.mul_ne_zero (by norm_num) hPpos.ne'
  have hHle : Nat.card H ≤ Nat.card ↥M.A := Nat.card_le_card_of_injective f hf
  have hcardP : Nat.card ↥M.P = Nat.card ↥N := (Nat.card_congr M.e.toEquiv).symm
  rw [h2, hcardP] at hHle
  have hidx : N.index * Nat.card ↥N = Nat.card H := Subgroup.index_mul_card (H := N)
  have hidxle : N.index ≤ 2 := by
    rw [← hidx] at hHle
    exact Nat.le_of_mul_le_mul_right hHle hNpos
  have hidx0 : N.index ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_mul] at hidx
    exact hHpos.ne' hidx.symm
  have hcases : N.index = 1 ∨ N.index = 2 := by omega
  rcases hcases with h1 | h2idx
  · exact Or.inr (Subgroup.index_eq_one.1 h1)
  · left
    have hcard : Nat.card ↥M.A = Nat.card H := by
      rw [h2, hcardP, ← hidx, h2idx]
    refine ⟨MulEquiv.ofBijective f (hf.bijective_of_nat_card_le (le_of_eq hcard))⟩

theorem AutModel.e8GenFacts {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Subgroup.centralizer (N : Set H) = ⊥) {G : Type*} [Group G] (M : AutModel N G)
    (h2 : Nat.card M.A = 2 * Nat.card M.P) (hA : E8GenFacts ↥M.A)
    (hP : ∀ B : Subgroup G, B ≤ M.P → (∀ b ∈ B, b ^ 2 = 1) → ¬ 8 ≤ Nat.card B) :
    E8GenFacts H := by
  have hP' : E8GenFacts ↥M.P := by
    intro B hB2 hB8
    have hB2' : ∀ b ∈ B.map M.P.subtype, b ^ 2 = 1 := by
      rintro b ⟨x, hx, rfl⟩
      have hx2 := hB2 x hx
      simpa using congrArg (fun y : ↥M.P => (y : G)) hx2
    have hcard : Nat.card (B.map M.P.subtype) = Nat.card B :=
      Subgroup.card_map_of_injective M.P.subtype_injective
    exact (hP (B.map M.P.subtype) (Subgroup.map_subtype_le B) hB2'
      (by rw [hcard]; exact hB8)).elim
  rcases M.nonempty_mulEquiv_or_eq_top N hN h2 with h | htop
  · obtain ⟨e⟩ := h
    exact E8GenFacts.of_mulEquiv e hA
  · let eH : H ≃* ↥N := (Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr htop).symm
    exact E8GenFacts.of_mulEquiv (eH.trans M.e) hP'

end CFSG.GH74.KGroups
