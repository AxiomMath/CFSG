module

public import CFSG.ClassicalInvolution.Q3.TL4D1MBaseC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Wr Equiv

variable {m : ℕ}

theorem aeModel_eq (m : ℕ) : aeModel m = aeBarOver (alternatingGroup (Fin m)) := by
  unfold aeModel aeBarOver aeSubOver
  congr 1
  ext a
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Perm.mem_alternatingGroup]
  exact ⟨fun h => ⟨h, h.2⟩, fun h => h.1⟩

theorem alt_pairTrans (hm : 5 ≤ m) : PairTrans (alternatingGroup (Fin m)) := by
  intro j k hjk
  classical
  set s := (Finset.univ.erase j).erase k with hs
  have hs3 : 3 ≤ s.card := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨fun h => hjk h.symm,
      Finset.mem_univ k⟩), Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hs2 : 2 ≤ (s.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < (s.erase i).card)
  simp only [hs, Finset.mem_erase, Finset.mem_univ, and_true] at hi hl
  obtain ⟨hik, hij⟩ := hi
  obtain ⟨hli, hlk, hlj⟩ := hl
  refine ⟨swap k l * swap k j, ?_, i, hik, ?_, ?_⟩
  · exact (Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hlk) hjk.symm hlj).mem_alternatingGroup
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hik hij, swap_apply_of_ne_of_ne hik hli.symm]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hjk hlj.symm]

theorem alt_normal_not_two (hm : 5 ≤ m) : ∀ Q : Subgroup (Perm (Fin m)),
    Q ≤ alternatingGroup (Fin m) → (∀ g ∈ alternatingGroup (Fin m), ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) →
    ¬ IsPGroup 2 Q → Q = alternatingGroup (Fin m) := by
  intro Q hQ hQn h2
  have hs := alternatingGroup.isSimpleGroup (α := Fin m) (by rw [Nat.card_fin]; exact hm)
  have : (Q.subgroupOf (alternatingGroup (Fin m))).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr (hQn g g.2 x (Subgroup.mem_subgroupOf.mp hx))⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.subgroupOf (alternatingGroup (Fin m)))
    with h | h
  · exfalso
    apply h2
    have hQb : Q = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hQ hx⟩ : ↥(alternatingGroup (Fin m))) ∈ Q.subgroupOf _ :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    rw [hQb]
    exact IsPGroup.of_bot
  · refine le_antisymm hQ fun x hx => ?_
    have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin m))) ∈ Q.subgroupOf _ := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem alt_sign : ∀ σ ∈ alternatingGroup (Fin m), Perm.sign σ = 1 :=
  fun _ h => Perm.mem_alternatingGroup.mp h

theorem aeNormal (m : ℕ) (hm : 5 ≤ m) : ModelNormal (aeModel m) := by
  rw [aeModel_eq]
  exact aeBarOver_normal alt_sign (alt_normal_not_two hm) (alt_pairTrans hm)

theorem aePerfect (m : ℕ) (hm : 5 ≤ m) : ModelPerfect (aeModel m) := by
  rw [aeModel_eq]
  exact aeBarOver_perfect alt_sign
    (commutator_alternatingGroup_eq_self (by rw [Nat.card_fin]; exact hm)) (alt_pairTrans hm)

end CFSG.ClassicalInvolution.Q3.TL4
