module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding.SPLMSide

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem p_mul_card_le {p : ℕ} [hp : Fact p.Prime] {H K : Subgroup G} (hK : IsPGroup p K)
    (hHK : H ≤ K) (hne : ¬ K ≤ H) : p * Nat.card H ≤ Nat.card K := by
  obtain ⟨n, hn⟩ := hK.index (H.subgroupOf K)
  have hrel : H.relIndex K = p ^ n := hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.relIndex_eq_one] at hrel
    exact hne hrel
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [inf_of_le_left hHK, hrel] at h1
  rw [← h1]
  apply Nat.mul_le_mul_right
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos (Nat.one_le_iff_ne_zero.mpr hn0)

theorem p_mul_card_closure_le {p : ℕ} [Fact p.Prime] {s : Set G} {w : G} {A D : Subgroup G}
    (hA : IsPGroup p A) (hsA : s ⊆ A) (hwA : w ∈ A) (hsD : s ⊆ D) (hwD : w ∉ D) :
    p * Nat.card (closure s) ≤ Nat.card (closure (insert w s)) := by
  have hle : closure (insert w s) ≤ A := (closure_le A).mpr (Set.insert_subset hwA hsA)
  refine p_mul_card_le (hA.to_le hle) (closure_mono (Set.subset_insert w s)) ?_
  intro h
  exact hwD ((closure_le D).mpr hsD (h (subset_closure (Set.mem_insert w s))))

omit [Finite G] in
theorem elemAbelian_closure {p : ℕ} {s : Set G} (hcomm : s.Pairwise Commute)
    (hp : ∀ x ∈ s, x ^ p = 1) : CFSG.Open.IsElemAbelian p (closure s) := by
  have hab := isMulCommutative_closure hcomm
  refine ⟨hab, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul a b ha hb iha ihb =>
    have hc : Commute a b := by
      have := hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    rw [hc.mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem six_le_card_closure {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : Nat.card X = p ^ 2)
    (w : ℕ → G) (D : ℕ → Subgroup G)
    (hA : IsPGroup p (closure (insert (w 4) (insert (w 3) (insert (w 2)
      (insert (w 1) (X : Set G)))))))
    (hXD : ∀ i, X ≤ D i) (hwD : ∀ k i, 1 ≤ k → k < i → i ≤ 4 → w k ∈ D i)
    (hwnD : ∀ i, 1 ≤ i → i ≤ 4 → w i ∉ D i) :
    p ^ 6 ≤ Nat.card (closure (insert (w 4) (insert (w 3) (insert (w 2)
      (insert (w 1) (X : Set G)))))) := by
  set s1 : Set G := insert (w 1) (X : Set G) with hs1
  set s2 : Set G := insert (w 2) s1 with hs2
  set s3 : Set G := insert (w 3) s2 with hs3
  set s4 : Set G := insert (w 4) s3 with hs4
  have h34 : s3 ⊆ s4 := Set.subset_insert _ _
  have h23 : s2 ⊆ s4 := (Set.subset_insert _ _).trans h34
  have h12 : s1 ⊆ s4 := (Set.subset_insert _ _).trans h23
  have h01 : (X : Set G) ⊆ s4 := (Set.subset_insert _ _).trans h12
  have hsub : ∀ s ⊆ s4, s ⊆ (closure s4 : Set G) := fun s hs => hs.trans Subgroup.subset_closure
  have hmem : ∀ i, 1 ≤ i → i ≤ 4 → w i ∈ closure s4 := by
    intro i hi1 hi4
    apply Subgroup.subset_closure
    simp only [hs4, hs3, hs2, hs1, Set.mem_insert_iff]
    interval_cases i <;> tauto
  have hD1 : ∀ i, 1 ≤ i → i ≤ 4 → s1 ⊆ D i ∨ i = 1 := by
    intro i hi1 hi4
    by_cases hi : i = 1
    · exact Or.inr hi
    left
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hwD 1 i le_rfl (by omega) hi4
    · exact hXD i hx
  have c0 : Nat.card (closure (X : Set G)) = p ^ 2 := by rw [Subgroup.closure_eq, hX]
  have c1 : p * Nat.card (closure (X : Set G)) ≤ Nat.card (closure s1) :=
    p_mul_card_closure_le hA (hsub _ h01) (hmem 1 le_rfl (by norm_num)) (hXD 1)
      (hwnD 1 le_rfl (by norm_num))
  have c2 : p * Nat.card (closure s1) ≤ Nat.card (closure s2) := by
    refine p_mul_card_closure_le hA (hsub _ h12) (hmem 2 (by norm_num) (by norm_num)) ?_
      (hwnD 2 (by norm_num) (by norm_num))
    exact (hD1 2 (by norm_num) (by norm_num)).resolve_right (by norm_num)
  have c3 : p * Nat.card (closure s2) ≤ Nat.card (closure s3) := by
    refine p_mul_card_closure_le hA (hsub _ h23) (hmem 3 (by norm_num) (by norm_num)) ?_
      (hwnD 3 (by norm_num) (by norm_num))
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hwD 2 3 (by norm_num) (by norm_num) (by norm_num)
    · exact (hD1 3 (by norm_num) (by norm_num)).resolve_right (by norm_num) hx
  have c4 : p * Nat.card (closure s3) ≤ Nat.card (closure s4) := by
    refine p_mul_card_closure_le hA (hsub _ h34) (hmem 4 (by norm_num) le_rfl) ?_
      (hwnD 4 (by norm_num) le_rfl)
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hwD 3 4 (by norm_num) (by norm_num) le_rfl
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hwD 2 4 (by norm_num) (by norm_num) le_rfl
    · exact (hD1 4 (by norm_num) le_rfl).resolve_right (by norm_num) hx
  rw [c0] at c1
  calc p ^ 6 = p * (p * (p * (p * p ^ 2))) := by ring
    _ ≤ p * (p * (p * Nat.card (closure s1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c1))
    _ ≤ p * (p * Nat.card (closure s2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c2)
    _ ≤ p * Nat.card (closure s3) := Nat.mul_le_mul_left _ c3
    _ ≤ Nat.card (closure s4) := c4

end CFSG.AGLEmbedding.SPLMSide
