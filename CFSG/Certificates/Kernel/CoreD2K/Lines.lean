
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Lines

public section

namespace CFSG.KD.CoreD2K

open CFSG.Open CFSG.AGLEmbedding.CoreD2

variable {X : Type*} [Group X] [Finite X]

theorem closure_pair_eq_of_mem {p : ℕ} (hp : p.Prime) {z x : X} {Y : Subgroup X}
    (hZ : Nat.card (Subgroup.zpowers z) = p) (hY : Nat.card Y = p ^ 2) (hzY : z ∈ Y)
    (hxY : x ∈ Y) (hxZ : x ∉ Subgroup.zpowers z) :
    Subgroup.closure ({z, x} : Set X) = Y := by
  have hWY : Subgroup.closure ({z, x} : Set X) ≤ Y := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hzY, hxY⟩
  have hZW : Subgroup.zpowers z ≤ Subgroup.closure ({z, x} : Set X) :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hxW : x ∈ Subgroup.closure ({z, x} : Set X) := Subgroup.subset_closure (by simp)
  have h1 : Nat.card (Subgroup.closure ({z, x} : Set X)) ∣ p ^ 2 :=
    hY ▸ Subgroup.card_dvd_of_le hWY
  have h2 : p ∣ Nat.card (Subgroup.closure ({z, x} : Set X)) :=
    hZ ▸ Subgroup.card_dvd_of_le hZW
  obtain ⟨k, hk, hkW⟩ := (Nat.dvd_prime_pow hp).1 h1
  have hk2 : k = 2 := by
    interval_cases k
    · rw [hkW, pow_zero] at h2
      exact absurd (Nat.le_of_dvd one_pos h2) (by have := hp.two_le; omega)
    · exfalso
      apply hxZ
      have e : Subgroup.zpowers z = Subgroup.closure ({z, x} : Set X) :=
        Subgroup.eq_of_le_of_card_ge hZW (by rw [hkW, hZ, pow_one])
      rw [e]
      exact hxW
    · rfl
  exact Subgroup.eq_of_le_of_card_ge hWY (by rw [hY, hkW, hk2])

theorem mem_lines_of_distinct {p : ℕ} (hp : p.Prime) {E : Subgroup X} (hE : Nat.card E = p ^ 3)
    {z : X} (hzE : z ∈ E) (hzp : z ^ p = 1) (hz1 : z ≠ 1) {v : ℕ → X}
    (hv : ∀ i ≤ p, v i ∈ E ∧ v i ^ p = 1 ∧ z * v i = v i * z ∧ ∀ k < p, v i ≠ z ^ k)
    (hd : ∀ j ≤ p, ∀ i < j, v j ∉ Subgroup.closure ({z, v i} : Set X)) :
    ∀ t ∈ E, ∃ i ≤ p, t ∈ Subgroup.closure ({z, v i} : Set X) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite X
  have hZ : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  have hYc : ∀ i ≤ p, Nat.card (Subgroup.closure ({z, v i} : Set X)) = p ^ 2 := fun i hi =>
    card_closure_pair_of_pow hp hzp (hv i hi).2.1 (hv i hi).2.2.1 hz1 (hv i hi).2.2.2
  have hzY : ∀ i, z ∈ Subgroup.closure ({z, v i} : Set X) := fun i =>
    Subgroup.subset_closure (by simp)
  have hvY : ∀ i, v i ∈ Subgroup.closure ({z, v i} : Set X) := fun i =>
    Subgroup.subset_closure (by simp)
  have hYE : ∀ i ≤ p, Subgroup.closure ({z, v i} : Set X) ≤ E := fun i hi => by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hzE, (hv i hi).1⟩
  have hZY : ∀ i, Subgroup.zpowers z ≤ Subgroup.closure ({z, v i} : Set X) := fun i =>
    Subgroup.zpowers_le.2 (hzY i)
  have hmeet : ∀ i ≤ p, ∀ j ≤ p, i ≠ j → ∀ x ∈ Subgroup.closure ({z, v i} : Set X),
      x ∈ Subgroup.closure ({z, v j} : Set X) → x ∈ Subgroup.zpowers z := by
    intro i hi j hj hij x hxi hxj
    by_contra hxZ
    have e : Subgroup.closure ({z, v i} : Set X) = Subgroup.closure ({z, v j} : Set X) :=
      (closure_pair_eq_of_mem hp hZ (hYc i hi) (hzY i) hxi hxZ).symm.trans
        (closure_pair_eq_of_mem hp hZ (hYc j hj) (hzY j) hxj hxZ)
    rcases lt_or_gt_of_ne hij with h | h
    · exact hd j hj i h (by rw [e]; exact hvY j)
    · exact hd i hi j h (by rw [← e]; exact hvY i)
  intro t ht
  by_contra hno
  push Not at hno
  have hcard : ∀ H : Subgroup X, Nat.card H = (Finset.univ.filter (· ∈ H)).card := fun H => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set D : ℕ → Finset X := fun i => (Finset.univ.filter (· ∈ Subgroup.closure ({z, v i} : Set X))) \
    (Finset.univ.filter (· ∈ Subgroup.zpowers z)) with hD
  have hsubZ : ∀ i, Finset.univ.filter (· ∈ Subgroup.zpowers z) ⊆
      Finset.univ.filter (· ∈ Subgroup.closure ({z, v i} : Set X)) := fun i x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hZY i hx
  have hDc : ∀ i ∈ Finset.range (p + 1), (D i).card = p ^ 2 - p := fun i hi => by
    have hi' : i ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [hD, Finset.card_sdiff_of_subset (hsubZ i), ← hcard, ← hcard, hYc i hi', hZ]
  have hdisj : ∀ i ∈ Finset.range (p + 1), ∀ j ∈ Finset.range (p + 1), i ≠ j →
      Disjoint (D i) (D j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [hD, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
    exact hxi.2 (hmeet i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) j
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hij x hxi.1 hxj.1)
  have hsub : (Finset.range (p + 1)).biUnion D ⊆
      Finset.univ.filter (· ∈ E) \ Finset.univ.filter (· ∈ Subgroup.zpowers z) := by
    intro x hx
    obtain ⟨i, hi, hxD⟩ := Finset.mem_biUnion.1 hx
    simp only [hD, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hxD ⊢
    exact ⟨hYE i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hxD.1, hxD.2⟩
  have htmem : t ∈ Finset.univ.filter (· ∈ E) \ Finset.univ.filter (· ∈ Subgroup.zpowers z) := by
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ht, fun h => hno 0 (Nat.zero_le p) (hZY 0 h)⟩
  have htD : t ∉ (Finset.range (p + 1)).biUnion D := by
    intro h
    obtain ⟨i, hi, hxD⟩ := Finset.mem_biUnion.1 h
    simp only [hD, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hxD
    exact hno i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hxD.1
  have hlt := Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨t, htmem, htD⟩)
  have hZE : Finset.univ.filter (· ∈ Subgroup.zpowers z) ⊆ Finset.univ.filter (· ∈ E) :=
    fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hYE 0 (Nat.zero_le p) (hZY 0 hx)
  rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hDc, Finset.sum_const, Finset.card_range,
    smul_eq_mul, Finset.card_sdiff_of_subset hZE, ← hcard, ← hcard, hE, hZ] at hlt
  have hp1 : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
  have hp3 : p ≤ p ^ 3 := Nat.le_self_pow (by norm_num) p
  zify [hp1, hp3] at hlt
  nlinarith

theorem eq_line_of_elemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup X} (hE : Nat.card E = p ^ 3)
    (hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) {z : X} (hzE : z ∈ E) (hzp : z ^ p = 1)
    (hz1 : z ≠ 1) (hzc : ∀ x ∈ E, x * z = z * x) {v : ℕ → X}
    (hv : ∀ i ≤ p, v i ∈ E ∧ v i ^ p = 1 ∧ z * v i = v i * z ∧ ∀ k < p, v i ≠ z ^ k)
    (hd : ∀ j ≤ p, ∀ i < j, v j ∉ Subgroup.closure ({z, v i} : Set X)) {A : Subgroup X}
    (hAE : A ≤ E) (hAe : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ i ≤ p, Subgroup.closure ({z, v i} : Set X) = A := by
  have : Fact p.Prime := ⟨hp⟩
  have hzA : z ∈ A := mem_of_central hp hE hnc hAE hAe hAc hzE hzc
  have hZ : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  obtain ⟨t, htA, htz⟩ : ∃ t ∈ A, t ∉ Subgroup.zpowers z := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ Subgroup.zpowers z := fun t ht => hcon t ht
    have h1 := Subgroup.card_le_of_le hle
    rw [hAc, hZ] at h1
    have h2 := hp.two_le
    nlinarith
  obtain ⟨i, hi, hti⟩ := mem_lines_of_distinct hp hE hzE hzp hz1 hv hd t (hAE htA)
  refine ⟨i, hi, ?_⟩
  have hYi := closure_pair_eq_of_mem hp hZ
    (card_closure_pair_of_pow hp hzp (hv i hi).2.1 (hv i hi).2.2.1 hz1 (hv i hi).2.2.2)
    (Subgroup.subset_closure (by simp)) hti htz
  have hle : Subgroup.closure ({z, t} : Set X) ≤ A := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hzA, htA⟩
  rw [← hYi]
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [hAc, hYi, card_closure_pair_of_pow hp hzp (hv i hi).2.1 (hv i hi).2.2.1 hz1
      (hv i hi).2.2.2])

end CFSG.KD.CoreD2K

end
