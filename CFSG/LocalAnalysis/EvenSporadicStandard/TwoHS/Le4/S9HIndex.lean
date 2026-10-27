module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S7Fusion

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type*} [Group G]

theorem relindex_le_four {L N : Subgroup G} {f y : G}
    (_hLN : L ≤ N) (hcom : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L) (hyy : y * y = 1)
    (hyn : y ∈ normalizer (L : Set G)) (hN : N = (L ⊔ zpowers f) ⊔ zpowers y)
    (hyf : y * f * y⁻¹ ∈ L ⊔ zpowers f) : L.relIndex N ≤ 4 := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hyL : ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun l hl => (mem_normalizer_iff.1 hyn l).1 hl
  have hA : ∀ a ∈ L ⊔ zpowers f, y * a * y⁻¹ ∈ L ⊔ zpowers f := by
    intro a ha
    obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup hcom ha
    have e : y * (l * f ^ i) * y⁻¹ = (y * l * y⁻¹) * (y * f * y⁻¹) ^ i := by
      rw [conj_zpow]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hyL l hl)) (zpow_mem hyf i)
  have hf2z : ∀ k : ℤ, f ^ (2 * k) ∈ L := fun k => by
    rw [zpow_mul]
    exact zpow_mem (by simpa using hf2) k
  have hdec : ∀ x ∈ N, ∃ l ∈ L, x = l ∨ x = l * f ∨ x = l * y ∨ x = l * f * y := by
    intro x hx
    rw [hN] at hx
    rcases mem_or_exists_of_mem_sup_zpowers hyy hA hx with h | ⟨a, ha, rfl⟩
    · obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup hcom h
      rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
      · exact ⟨l * f ^ (2 * k), L.mul_mem hl (hf2z k), Or.inl rfl⟩
      · refine ⟨l * f ^ (2 * k), L.mul_mem hl (hf2z k), Or.inr (Or.inl ?_)⟩
        rw [zpow_add_one, mul_assoc]
    · obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup hcom ha
      rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
      · exact ⟨l * f ^ (2 * k), L.mul_mem hl (hf2z k), Or.inr (Or.inr (Or.inl rfl))⟩
      · refine ⟨l * f ^ (2 * k), L.mul_mem hl (hf2z k), Or.inr (Or.inr (Or.inr ?_))⟩
        rw [zpow_add_one]
        group
  have hfN : f ∈ N := by
    rw [hN]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers f))
  have hyN : y ∈ N := by
    rw [hN]
    exact Subgroup.mem_sup_right (mem_zpowers y)
  have c1 : ∀ l ∈ L, f⁻¹ * (l * f) ∈ L := fun l hl => by
    have : f⁻¹ * (l * f) = l := by rw [hcom l hl]; group
    rw [this]
    exact hl
  have c2 : ∀ l ∈ L, y⁻¹ * (l * y) ∈ L := fun l hl => by
    have : y⁻¹ * (l * y) = y * l * y⁻¹ := by rw [hyinv]; group
    rw [this]
    exact hyL l hl
  have c3 : ∀ l ∈ L, (f * y)⁻¹ * (l * f * y) ∈ L := fun l hl => by
    have h1 : f⁻¹ * (l * f) = l := by rw [hcom l hl]; group
    have : (f * y)⁻¹ * (l * f * y) = y * l * y⁻¹ := by
      calc (f * y)⁻¹ * (l * f * y) = y⁻¹ * (f⁻¹ * (l * f)) * y := by group
        _ = y⁻¹ * l * y := by rw [h1]
        _ = y * l * y⁻¹ := by rw [hyinv]
    rw [this]
    exact hyL l hl
  let reps : Fin 4 → N := ![1, ⟨f, hfN⟩, ⟨y, hyN⟩, ⟨f * y, N.mul_mem hfN hyN⟩]
  let ρ : Fin 4 → ↥N ⧸ L.subgroupOf N := fun i => (reps i : ↥N ⧸ L.subgroupOf N)
  have hsurj : Function.Surjective ρ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨l, hl, h | h | h | h⟩ := hdec (x : G) x.2
      · refine ⟨0, QuotientGroup.eq.2 ?_⟩
        rw [Subgroup.mem_subgroupOf]
        simpa [reps, h] using hl
      · refine ⟨1, QuotientGroup.eq.2 ?_⟩
        rw [Subgroup.mem_subgroupOf]
        simpa [reps, h] using c1 l hl
      · refine ⟨2, QuotientGroup.eq.2 ?_⟩
        rw [Subgroup.mem_subgroupOf]
        simpa [reps, h] using c2 l hl
      · refine ⟨3, QuotientGroup.eq.2 ?_⟩
        rw [Subgroup.mem_subgroupOf]
        simpa [reps, h] using c3 l hl
  calc L.relIndex N = Nat.card (↥N ⧸ L.subgroupOf N) := Subgroup.index_eq_card _
    _ ≤ Nat.card (Fin 4) := Nat.card_le_card_of_surjective ρ hsurj
    _ = 4 := by simp

theorem relindex_le_four_of_inv {L N : Subgroup G} {f y : G}
    (hLN : L ≤ N) (hcom : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L) (hyy : y * y = 1)
    (hyn : y ∈ normalizer (L : Set G)) (hN : N = (L ⊔ zpowers f) ⊔ zpowers y)
    (hyf : y * f * y⁻¹ = f⁻¹) : L.relIndex N ≤ 4 :=
  relindex_le_four hLN hcom hf2 hyy hyn hN
    (hyf ▸ Subgroup.mem_sup_right (inv_mem (mem_zpowers f)))

end CFSG.EvenSporadicStandard.TwoHS
