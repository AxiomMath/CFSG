module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem perp_center_closure_pair {a c : G} (ha : a ^ 2 = 1) (hc : c ^ 2 = 1) {k : ℕ} (hk : 2 ≤ k)
    (hord : orderOf (a * c) = 2 * k) (y : G) :
    (y ∈ centerOf (Subgroup.closure {a, c}) ∧ y ≠ 1) ↔ y = (a * c) ^ k := by
  let r : G := a * c
  have hr : r = a * c := rfl
  have haa : a * a = 1 := by simpa [pow_two] using ha
  have hcc : c * c = 1 := by simpa [pow_two] using hc
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hord' : orderOf r = 2 * k := by rw [hr]; exact hord
  have hs2 : (r ^ k) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, ← hord', pow_orderOf_eq_one]
  have hrk_ne_one : r ^ k ≠ 1 :=
    pow_ne_one_of_lt_orderOf (n := k) (by omega) (by rw [hord']; omega)
  have hs2z : (r ^ k) ^ (2 : ℤ) = 1 := by simpa using hs2
  have hsinv : (r ^ k)⁻¹ = r ^ k := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hs2
  have hconj : a * r * a⁻¹ = r⁻¹ := by
    have hl : a * r * a⁻¹ = c * a := by
      rw [hr, ← mul_assoc, haa, one_mul, hai]
    have hr' : r⁻¹ = c * a := by
      rw [hr, mul_inv_rev, hai, hci]
    rw [hl, hr']
  have hconj_mul : ∀ j : ℤ, a * r ^ j = r ^ (-j) * a := by
    intro j
    have h := congrArg (fun z => z ^ j) hconj
    rw [conj_zpow, inv_zpow'] at h
    have h2 := congrArg (fun z => z * a) h
    simpa [mul_assoc] using h2
  have hconj_nat : ∀ n : ℕ, a * r ^ n * a⁻¹ = (r ^ n)⁻¹ := by
    intro n
    have h := congrArg (fun z => z ^ n) hconj
    rwa [conj_pow, inv_pow] at h
  have har : a * r = r ^ (-1 : ℤ) * a := by
    have h := hconj_mul (1 : ℤ)
    rwa [zpow_one] at h
  have hs_pow : ∀ m : ℤ, (r ^ k) ^ m = 1 ∨ (r ^ k) ^ m = r ^ k := by
    intro m
    rcases Int.even_or_odd' m with ⟨t, ht | ht⟩
    · left
      rw [ht, zpow_mul, hs2z, one_zpow]
    · right
      rw [ht, zpow_add, zpow_mul, hs2z, one_zpow, zpow_one, one_mul]
  have hmul1 : ∀ i j : ℤ, r ^ i * r ^ j = r ^ (i + j) := fun i j => by rw [← zpow_add]
  have hmul2 : ∀ i j : ℤ, r ^ i * (r ^ j * a) = r ^ (i + j) * a := fun i j => by
    rw [← mul_assoc, ← zpow_add]
  have hmul3 : ∀ i j : ℤ, (r ^ i * a) * r ^ j = r ^ (i - j) * a := fun i j => by
    rw [mul_assoc, hconj_mul j, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
  have hmul4 : ∀ i j : ℤ, (r ^ i * a) * (r ^ j * a) = r ^ (i - j) := fun i j => by
    rw [← mul_assoc (r ^ i * a) (r ^ j) a, hmul3 i j, mul_assoc, haa, mul_one]
  have hnormal : ∀ x ∈ Subgroup.closure ({a, c} : Set G),
      (∃ i : ℤ, x = r ^ i) ∨ (∃ i : ℤ, x = r ^ i * a) := by
    intro x hx
    refine Subgroup.closure_induction (p := fun z _ =>
      (∃ i : ℤ, z = r ^ i) ∨ (∃ i : ℤ, z = r ^ i * a)) ?_ ?_ ?_ ?_ hx
    · intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Or.inr ⟨0, by rw [zpow_zero, one_mul]⟩
      · exact Or.inr ⟨-1, by
          rw [hr, zpow_neg_one, mul_inv_rev, hai, hci, mul_assoc, haa, mul_one]⟩
    · exact Or.inl ⟨0, by rw [zpow_zero]⟩
    · intro u v _ _ ihu ihv
      rcases ihu with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases ihv with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact Or.inl ⟨i + j, hmul1 i j⟩
      · exact Or.inr ⟨i + j, hmul2 i j⟩
      · exact Or.inr ⟨i - j, hmul3 i j⟩
      · exact Or.inl ⟨i - j, hmul4 i j⟩
    · intro u _ ihu
      rcases ihu with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact Or.inl ⟨-i, by rw [← inv_zpow, inv_zpow']⟩
      · exact Or.inr ⟨i, by
          rw [mul_inv_rev, hai, ← inv_zpow, inv_zpow', hconj_mul (-i), neg_neg]⟩
  have haH : a ∈ Subgroup.closure ({a, c} : Set G) := Subgroup.subset_closure (by simp)
  have hcH : c ∈ Subgroup.closure ({a, c} : Set G) := Subgroup.subset_closure (by simp)
  have hrH : r ∈ Subgroup.closure ({a, c} : Set G) := by
    rw [hr]; exact Subgroup.mul_mem _ haH hcH
  have hrs : r * r ^ k = r ^ k * r := by rw [← pow_succ', ← pow_succ]
  have hceq : c = a * r := by rw [hr, ← mul_assoc, haa, one_mul]
  have has : a * r ^ k = r ^ k * a := by
    have h := hconj_nat k
    rw [hsinv] at h
    have h2 := congrArg (fun z => z * a) h
    simpa [mul_assoc] using h2
  have hcs : c * r ^ k = r ^ k * c := by
    calc c * r ^ k = (a * r) * r ^ k := by rw [hceq]
      _ = a * (r * r ^ k) := by rw [mul_assoc]
      _ = a * (r ^ k * r) := by rw [hrs]
      _ = (a * r ^ k) * r := by rw [← mul_assoc]
      _ = (r ^ k * a) * r := by rw [has]
      _ = r ^ k * (a * r) := by rw [mul_assoc]
      _ = r ^ k * c := by rw [hceq]
  have hcentH : Subgroup.closure ({a, c} : Set G) ≤
      Subgroup.centralizer ({r ^ k} : Set G) := by
    rw [Subgroup.closure_le]
    intro u hu
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact has.symm
    · apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hcs.symm
  change (y ∈ centerOf (Subgroup.closure {a, c}) ∧ y ≠ 1) ↔ y = r ^ k
  constructor
  · intro hy
    have hy1 := hy.1
    rw [centerOf] at hy1
    have hyH : y ∈ Subgroup.closure ({a, c} : Set G) := hy1.1
    have hyC : y ∈ Subgroup.centralizer
        ((Subgroup.closure ({a, c} : Set G)) : Set G) := hy1.2
    have hay : a * y = y * a := (Subgroup.mem_centralizer_iff.mp hyC) a haH
    have hry : r * y = y * r := (Subgroup.mem_centralizer_iff.mp hyC) r hrH
    rcases hnormal y hyH with ⟨i, hyi⟩ | ⟨i, hyi⟩
    · have h1 : r ^ (-i) = r ^ i := by
        have h := hay
        rw [hyi, hconj_mul i] at h
        exact mul_right_cancel h
      have h2 : r ^ (2 * i) = 1 := by
        rw [show (2 : ℤ) * i = i + i by ring, zpow_add]
        have hii : r ^ i * r ^ i = r ^ i * r ^ (-i) := by rw [h1]
        rw [hii, ← zpow_add, add_neg_cancel, zpow_zero]
      have hdvd : (k : ℤ) ∣ i := by
        have hmem : (orderOf r : ℤ) ∣ 2 * i := orderOf_dvd_iff_zpow_eq_one.mpr h2
        rw [hord'] at hmem
        obtain ⟨m, hm⟩ := hmem
        refine ⟨m, ?_⟩
        have hcast : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; ring
        rw [hcast] at hm
        exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (by rw [hm]; ring)
      obtain ⟨m, hm⟩ := hdvd
      have hy_eq : y = (r ^ k) ^ m := by rw [hyi, hm, zpow_mul, zpow_natCast]
      rcases hs_pow m with hm1 | hm1
      · exact absurd (hy_eq.trans hm1) hy.2
      · rw [hy_eq]
        exact hm1
    · have h1 : r ^ (i + 1) = r ^ (i - 1) := by
        have hl : r * (r ^ i * a) = r ^ (i + 1) * a := by
          rw [← mul_assoc, ← zpow_one_add, add_comm]
        have hr2 : (r ^ i * a) * r = r ^ (i - 1) * a := by
          rw [mul_assoc, har, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
        have h := hry
        rw [hyi] at h
        rw [hl, hr2] at h
        exact mul_right_cancel h
      have hdvd2 : (orderOf r : ℤ) ∣ (2 : ℤ) := by
        have h := (orderOf_dvd_sub_iff_zpow_eq_zpow (x := r)).mpr h1
        have hsub : (i + 1) - (i - 1) = (2 : ℤ) := by ring
        rwa [hsub] at h
      have hr2one : r ^ (2 : ℤ) = 1 := orderOf_dvd_iff_zpow_eq_one.mp hdvd2
      exfalso
      exact (pow_ne_one_of_lt_orderOf (n := 2) (by norm_num)
        (by rw [hord']; omega)) (by simpa using hr2one)
  · intro hy
    have hyH : y ∈ Subgroup.closure ({a, c} : Set G) := by
      rw [hy]
      exact Subgroup.pow_mem _ hrH k
    have hycent : y ∈ Subgroup.centralizer
        ((Subgroup.closure ({a, c} : Set G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h' := hcentH hu
      rw [Subgroup.mem_centralizer_iff] at h'
      exact (h' y (Set.mem_singleton_iff.mpr hy)).symm
    constructor
    · rw [centerOf, Subgroup.mem_inf]
      exact ⟨hyH, hycent⟩
    · rw [hy]
      exact hrk_ne_one

end CFSG.EvenSporadicStandard.HNRecog.Section3
