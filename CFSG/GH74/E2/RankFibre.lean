module

public import CFSG.GH74.E2.FrattiniRank

public section

namespace CFSG.GH74.E2

open Subgroup

theorem rank_le_rank_add_one_of_index_two {T : Type*} [Group T] [Finite T] (P : Subgroup T)
    (h : P.index = 2) : Group.rank T ≤ Group.rank P + 1 := by
  classical
  obtain ⟨S0, hS0c, hS0⟩ := Group.rank_spec P
  obtain ⟨g, hg⟩ : ∃ g : T, g ∉ P := by
    by_contra hcon
    push Not at hcon
    have : P = ⊤ := eq_top_iff.2 fun g _ => hcon g
    rw [this, index_top] at h
    omega
  let S1 : Finset T := S0.image Subtype.val ∪ {g}
  have hcard : S1.card ≤ Group.rank P + 1 := by
    calc S1.card ≤ (S0.image Subtype.val).card + ({g} : Finset T).card :=
          Finset.card_union_le _ _
      _ ≤ S0.card + 1 := by
          rw [Finset.card_singleton]
          exact Nat.add_le_add_right Finset.card_image_le 1
      _ = Group.rank P + 1 := by rw [hS0c]
  have hPH : ∀ x : P, (x : T) ∈ closure (S1 : Set T) := by
    intro x
    have hx : x ∈ closure (S0 : Set P) := by
      rw [hS0]
      exact mem_top x
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      simp only [S1, Finset.coe_union, Finset.coe_image, Finset.coe_singleton, Set.mem_union,
        Set.mem_image, Finset.mem_coe]
      exact Or.inl ⟨y, hy, rfl⟩
    | one => exact (closure (S1 : Set T)).one_mem
    | mul a b _ _ ha hb => exact (closure (S1 : Set T)).mul_mem ha hb
    | inv a _ ha => exact (closure (S1 : Set T)).inv_mem ha
  have hgH : g ∈ closure (S1 : Set T) := by
    apply Subgroup.subset_closure
    simp [S1]
  have hclos : closure (S1 : Set T) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_cases hx : x ∈ P
    · exact hPH ⟨x, hx⟩
    · have hxg : x * g⁻¹ ∈ P := by
        rw [mul_mem_iff_of_index_two h]
        simp [hx, hg]
      have h1 : x * g⁻¹ ∈ closure (S1 : Set T) := hPH ⟨_, hxg⟩
      have h2 := (closure (S1 : Set T)).mul_mem h1 hgH
      simpa using h2
  exact (Group.rank_le hclos).trans hcard

theorem rank_add_le_of_disjoint {S : Type*} [Group S] [Finite S] (hS : IsPGroup 2 S)
    (M N : Subgroup S) [M.Normal] [N.Normal] (hdisj : M ⊓ N = ⊥)
    (hcard : Nat.card S = 2 * (Nat.card M * Nat.card N)) :
    Group.rank (S ⧸ M) + Group.rank (S ⧸ N) ≤ Group.rank S + 1 := by
  classical
  let f : S →* (S ⧸ M) × (S ⧸ N) := (QuotientGroup.mk' M).prod (QuotientGroup.mk' N)
  have hker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : x ∈ M := (QuotientGroup.eq_one_iff x).1 (congrArg Prod.fst hx)
    have h2 : x ∈ N := (QuotientGroup.eq_one_iff x).1 (congrArg Prod.snd hx)
    have : x ∈ M ⊓ N := ⟨h1, h2⟩
    rw [hdisj] at this
    exact this
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hker
  have hS0 : 0 < Nat.card S := Nat.card_pos
  have hM0 : 0 < Nat.card M := Nat.card_pos
  have hN0 : 0 < Nat.card N := Nat.card_pos
  have hSM : Nat.card (S ⧸ M) = 2 * Nat.card N := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M
    rw [hcard] at h1
    have : Nat.card (S ⧸ M) * Nat.card M = (2 * Nat.card N) * Nat.card M := by
      rw [← h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hM0 this
  have hSN : Nat.card (S ⧸ N) = 2 * Nat.card M := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcard] at h1
    have : Nat.card (S ⧸ N) * Nat.card N = (2 * Nat.card M) * Nat.card N := by
      rw [← h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hN0 this
  have hrange : Nat.card f.range = Nat.card S := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hindex : f.range.index = 2 := by
    have h1 := f.range.index_mul_card
    rw [hrange, Nat.card_prod, hSM, hSN] at h1
    have : f.range.index * Nat.card S = 2 * Nat.card S := by
      rw [h1, hcard]
      ring
    exact Nat.eq_of_mul_eq_mul_right hS0 this
  have hQM : IsPGroup 2 (S ⧸ M) := hS.to_quotient M
  have hQN : IsPGroup 2 (S ⧸ N) := hS.to_quotient N
  have h1 := rank_add_le_rank_prod hQM hQN
  have h2 := rank_le_rank_add_one_of_index_two f.range hindex
  have h3 : Group.rank f.range = Group.rank S :=
    (Group.rank_congr (MonoidHom.ofInjective hinj)).symm
  omega

end CFSG.GH74.E2
