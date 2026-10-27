module

public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm

def pairEW {n : ℕ} (i j : Fin n) : evenWeight n :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    rw [evenWeight, AddMonoidHom.mem_ker]
    simp [Finset.sum_add_distrib, Pi.single_apply]
    decide⟩

theorem pairEW_apply {n : ℕ} (i j p : Fin n) :
    ((pairEW i j : evenWeight n) : Fin n → ZMod 2) p =
      (if p = i then 1 else 0) + (if p = j then 1 else 0) := by
  simp [pairEW, Pi.single_apply]

theorem evenWeightPerm_pairEW_apply {n : ℕ} (σ : Perm (Fin n)) (i j p : Fin n) :
    ((evenWeightPerm σ (pairEW i j) : evenWeight n) : Fin n → ZMod 2) p =
      (if p = σ i then 1 else 0) + (if p = σ j then 1 else 0) := by
  have h1 : (σ⁻¹ p = i) ↔ (p = σ i) := by
    constructor
    · rintro h; rw [← h]; simp
    · rintro h; rw [h]; simp
  have h2 : (σ⁻¹ p = j) ↔ (p = σ j) := by
    constructor
    · rintro h; rw [← h]; simp
    · rintro h; rw [h]; simp
  show ((pairEW i j : evenWeight n) : Fin n → ZMod 2) (σ⁻¹ p) = _
  rw [pairEW_apply]
  simp only [h1, h2]

theorem exists_ne_four {n : ℕ} (hn : 5 ≤ n) (a b c d : Fin n) :
    ∃ e : Fin n, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c, d} := by
    intro e _
    by_cases h1 : e = a
    · simp [h1]
    by_cases h2 : e = b
    · simp [h2]
    by_cases h3 : e = c
    · simp [h3]
    simp [h e h1 h2 h3]
  have h4 := Finset.card_le_card hsub
  have h5 : ({a, b, c, d} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
  simp at h4
  omega

theorem perm_mem_of_pair_fixed {n : ℕ} (hn : 5 ≤ n) (σ : Perm (Fin n)) {i j : Fin n} (hij : i ≠ j)
    (h : (QuotientAddGroup.mk (evenWeightPerm σ (pairEW i j)) : altHeart n) =
      QuotientAddGroup.mk (pairEW i j)) : σ i = i ∨ σ i = j := by
  have hσ : σ i ≠ σ j := fun e => hij (σ.injective e)
  rw [QuotientAddGroup.eq] at h
  have hmem : (-(evenWeightPerm σ (pairEW i j)) + pairEW i j : evenWeight n) ∈
      evenWeightOnes n := h
  rw [evenWeightOnes, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  obtain ⟨q, hqi, hqj, hqσi, hqσj⟩ := exists_ne_four hn i j (σ i) (σ j)
  have hz : ∀ p : Fin n, (-(evenWeightPerm σ (pairEW i j)) + pairEW i j : evenWeight n).1 p =
      (k • allOnes n) p := fun p => congrFun hk.symm p
  have hq := hz q
  simp [evenWeightPerm_pairEW_apply, pairEW_apply, hqi, hqj, hqσi, hqσj] at hq
  have hp := hz (σ i)
  have hk0 : (k : ZMod 2) = 0 := by
    rcases hq with h | h
    · exact h
    · simp [allOnes] at h
  by_contra hno
  push Not at hno
  simp [evenWeightPerm_pairEW_apply, pairEW_apply, hno.1, hno.2, hσ, hk0] at hp

theorem perm_eq_one_of_altHeart_fixed {n : ℕ} (hn : 5 ≤ n) (σ : Perm (Fin n))
    (h : ∀ x : evenWeight n,
      (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) = QuotientAddGroup.mk x) :
    σ = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨j, hji, -, -, -⟩ := exists_ne_four hn i i i i
  obtain ⟨k, hki, hkj, -, -⟩ := exists_ne_four hn i j j j
  have h1 := perm_mem_of_pair_fixed hn σ (Ne.symm hji) (h (pairEW i j))
  have h2 := perm_mem_of_pair_fixed hn σ (Ne.symm hki) (h (pairEW i k))
  show σ i = i
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) (Ne.symm hkj |>.symm |> fun _ => hkj.symm)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
