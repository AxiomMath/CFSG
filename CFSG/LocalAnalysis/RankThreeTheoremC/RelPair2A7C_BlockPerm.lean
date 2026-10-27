module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup Equiv CFSG.RankThree.PartTwo.KFacts.KP2

theorem a7b_vOneF_spec : ∀ i : Fin 4,
    Perm.sign (vOneF i) = 1 ∧ vOneF i 1 = 1 ∧ vOneF i 2 = 2 ∧ vOneF i 0 = 0 := by
  decide +kernel

theorem a7b_vOne_le_a7Four : vOne ≤ a7Four := by
  rintro _ ⟨i, rfl⟩
  obtain ⟨h, h1, h2, h0⟩ := a7b_vOneF_spec i
  exact mem_a7Four_iff.2 ⟨Perm.mem_alternatingGroup.2 h, h1, h2, h0⟩

theorem a7b_cTwo_mem_a7Four : cTwo ∈ a7Four :=
  mem_a7Four_iff.2 ⟨Perm.mem_alternatingGroup.2 (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel⟩

theorem a7b_card_filter_a7Four_cases : (Finset.univ.filter (fun σ : Perm (Fin 7) =>
    σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ Perm.sign σ = 1 ∧
      ¬ ∃ i : Fin 4, ∃ k : Fin 3, σ = vOneF i * cTwo ^ (k : ℕ))).card = 0 := by
  decide +kernel

theorem a7b_a7Four_cases (σ : Perm (Fin 7)) (h0 : σ 0 = 0) (h1 : σ 1 = 1) (h2 : σ 2 = 2)
    (hs : Perm.sign σ = 1) : ∃ i : Fin 4, ∃ k : Fin 3, σ = vOneF i * cTwo ^ (k : ℕ) := by
  by_contra h
  exact forall_not_of_card_filter_eq_zero a7b_card_filter_a7Four_cases σ ⟨h0, h1, h2, hs, h⟩

theorem a7b_a7Four_le_sup : a7Four ≤ vOne ⊔ zpowers cTwo := by
  intro σ hσ
  obtain ⟨hA, h1, h2, h0⟩ := mem_a7Four_iff.1 hσ
  obtain ⟨i, k, rfl⟩ := a7b_a7Four_cases σ h0 h1 h2 (Perm.mem_alternatingGroup.1 hA)
  exact mul_mem (mem_sup_left ⟨i, rfl⟩) (mem_sup_right (pow_mem (mem_zpowers _) _))

theorem a7b_card_filter_a7Five : (Finset.univ.filter (fun σ : Perm (Fin 7) =>
    σ 1 = 1 ∧ σ 2 = 2 ∧ Perm.sign σ = 1)).card = 60 := by
  decide +kernel

theorem a7b_card_filter_a7Four : (Finset.univ.filter (fun σ : Perm (Fin 7) =>
    σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ Perm.sign σ = 1)).card = 12 := by
  decide +kernel

theorem a7b_card_a7Five : Nat.card a7Five = 60 := by
  rw [← a7b_card_filter_a7Five, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
  rw [mem_a7Five_iff, Perm.mem_alternatingGroup]
  tauto

theorem a7b_card_a7Four : Nat.card a7Four = 12 := by
  rw [← a7b_card_filter_a7Four, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
  rw [mem_a7Four_iff, Perm.mem_alternatingGroup]
  tauto

theorem a7b_eq_or_eq_of_le {X : Subgroup (Perm (Fin 7))} (h4 : a7Four ≤ X) (h5 : X ≤ a7Five) :
    X = a7Four ∨ X = a7Five := by
  have hd4 : 12 ∣ Nat.card X := a7b_card_a7Four ▸ Subgroup.card_dvd_of_le h4
  have hd5 : Nat.card X ∣ 60 := a7b_card_a7Five ▸ Subgroup.card_dvd_of_le h5
  have key : ∀ n ∈ Nat.divisors 60, 12 ∣ n → n = 12 ∨ n = 60 := by decide
  rcases key _ (Nat.mem_divisors.2 ⟨hd5, by norm_num⟩) hd4 with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h4 (by rw [h, a7b_card_a7Four])).symm
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h5 (by rw [h, a7b_card_a7Five]))

@[expose] def a7b_fiveCycle : Perm (Fin 7) := sw 0 3 * sw 3 4 * sw 4 5 * sw 5 6

theorem a7b_fiveCycle_mem : a7b_fiveCycle ∈ a7Five :=
  mem_a7Five_iff.2 ⟨Perm.mem_alternatingGroup.2 (by decide +kernel), by decide +kernel,
    by decide +kernel⟩

theorem a7b_sevenCycle_pow :
    ∀ x : Fin 7, ∃ k : Fin 7, ((cOne * a7b_fiveCycle) ^ (k : ℕ)) 0 = x := by
  decide +kernel

theorem a7b_alternatingGroup_le_sup : alternatingGroup (Fin 7) ≤ a7Five ⊔ eNine := by
  set J := a7Five ⊔ eNine
  have hz : cOne * a7b_fiveCycle ∈ J :=
    mul_mem (mem_sup_right cOne_mem_eNine) (mem_sup_left a7b_fiveCycle_mem)
  have htr : MulAction.IsPretransitive J (Fin 7) := by
    rw [MulAction.isPretransitive_iff_base (0 : Fin 7)]
    intro x
    obtain ⟨k, hk⟩ := a7b_sevenCycle_pow x
    exact ⟨⟨_, pow_mem hz k⟩, hk⟩
  have hpr : MulAction.IsPreprimitive J (Fin 7) := MulAction.IsPreprimitive.of_prime_card
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have h3 : (swap (0 : Fin 7) 4 * swap 0 3).IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  refine Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hpr h3 (mem_sup_left ?_)
  exact mem_a7Five_iff.2 ⟨h3.mem_alternatingGroup, by decide +kernel, by decide +kernel⟩

theorem a7b_mem_a7Five_not_mem_a7Four :
    swap (0 : Fin 7) 4 * swap 0 3 ∈ a7Five ∧ swap (0 : Fin 7) 4 * swap 0 3 ∉ a7Four := by
  refine ⟨mem_a7Five_iff.2 ⟨(Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide)
    (by decide)).mem_alternatingGroup, by decide +kernel, by decide +kernel⟩, fun h => ?_⟩
  have := (mem_a7Four_iff.1 h).2.2.2
  revert this
  decide +kernel

end CFSG.LocalAnalysis.RankThreeTheoremC
