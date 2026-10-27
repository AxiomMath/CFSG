module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Equiv

section SwapLemmas

variable {α : Type*} [DecidableEq α]

theorem swap_mul_swap_ne_comm {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    swap x y * swap x z ≠ swap x z * swap x y := by
  intro h
  have h0 := congrArg (fun p : Perm α => p x) h
  simp only [Perm.mul_apply] at h0
  have h1 : swap x y (swap x z x) = z := by
    rw [swap_apply_left]; exact swap_apply_of_ne_of_ne hxz.symm hyz.symm
  have h2 : swap x z (swap x y x) = y := by
    rw [swap_apply_left]; exact swap_apply_of_ne_of_ne hxy.symm hyz
  exact hyz (h1.symm.trans (h0.trans h2)).symm

theorem swap_mul_swap_ne_comm' {i j k : α} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    swap i j * swap j k ≠ swap j k * swap i j := by
  rw [swap_comm i j]
  exact swap_mul_swap_ne_comm hij.symm hjk hik

theorem swap_mul_swap_mul_swap_eq {i j k : α} (hjk : j ≠ k) (hik : i ≠ k) :
    swap i j * swap j k * swap i j = swap i k := by
  have := Equiv.swap_mul_swap_mul_swap (x := k) (y := j) (z := i) hjk.symm hik.symm
  rwa [swap_comm j i, swap_comm k j] at this

theorem exists_perm_apply_eq_of_ne {i j k l : α} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ π : Perm α, π i = k ∧ π j = l := by
  have hj'k : swap i k j ≠ k := by
    intro h
    have : swap i k j = swap i k i := by rw [swap_apply_left]; exact h
    exact hij ((swap i k).injective this).symm
  refine ⟨swap (swap i k j) l * swap i k, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_left]
    exact swap_apply_of_ne_of_ne hj'k.symm hkl
  · rw [Perm.mul_apply, swap_apply_left]

theorem exists_perm_swap_conj {i j k l : α} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ π : Perm α, π * swap i j * π⁻¹ = swap k l := by
  obtain ⟨π, h1, h2⟩ := exists_perm_apply_eq_of_ne hij hkl
  exact ⟨π, by rw [← swap_apply_apply, h1, h2]⟩

theorem swap_pair_cases {i j k l : α} (hij : i ≠ j) (hkl : k ≠ l) (hne : swap i j ≠ swap k l)
    (hnd : ¬(i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l)) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ swap i j = swap a b ∧ swap k l = swap a c := by
  by_cases h1 : i = k
  · refine ⟨i, j, l, hij, h1 ▸ hkl, fun h => hne ?_, rfl, by rw [h1]⟩
    rw [h1, h]
  · by_cases h2 : i = l
    · refine ⟨i, j, k, hij, h1, fun h => hne ?_, rfl, by rw [h2, swap_comm]⟩
      rw [← h, h2, swap_comm]
    · by_cases h3 : j = k
      · refine ⟨j, i, l, hij.symm, h3 ▸ hkl, fun h => hne ?_, swap_comm _ _, by rw [h3]⟩
        rw [swap_comm, h, h3]
      · by_cases h4 : j = l
        · refine ⟨j, i, k, hij.symm, h3, h1, swap_comm _ _, by rw [h4, swap_comm]⟩
        · exact absurd ⟨h1, h2, h3, h4⟩ hnd

theorem swap_mul_swap_pow_three [Fintype α] {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : (swap x y * swap x z) ^ 3 = 1 := by
  have h3 := Equiv.Perm.isThreeCycle_swap_mul_swap_same hxy hxz hyz
  have := pow_orderOf_eq_one (swap x y * swap x z)
  rwa [h3.orderOf] at this

theorem swap_pair_trichotomy [Fintype α] {i j k l : α} (hij : i ≠ j) (hkl : k ≠ l) :
    swap i j = swap k l ∨
    ((i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l) ∧ swap i j * swap k l = swap k l * swap i j) ∨
    (swap i j * swap k l ≠ swap k l * swap i j ∧ (swap i j * swap k l) ^ 3 = 1) := by
  by_cases hne : swap i j = swap k l
  · exact Or.inl hne
  by_cases hnd : (i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l)
  · refine Or.inr (Or.inl ⟨hnd, ?_⟩)
    have hd : Perm.Disjoint (swap i j) (swap k l) := fun x => by
      by_cases hxi : x = i
      · right; subst hxi; exact swap_apply_of_ne_of_ne hnd.1 hnd.2.1
      · by_cases hxj : x = j
        · right; subst hxj; exact swap_apply_of_ne_of_ne hnd.2.2.1 hnd.2.2.2
        · left; exact swap_apply_of_ne_of_ne hxi hxj
    exact hd.commute
  · obtain ⟨a, b, c, hab, hac, hbc, e1, e2⟩ := swap_pair_cases hij hkl hne hnd
    refine Or.inr (Or.inr ?_)
    rw [e1, e2]
    exact ⟨swap_mul_swap_ne_comm hab hac hbc, swap_mul_swap_pow_three hab hac hbc⟩

theorem swap_comm_of_pow_four [Fintype α] {i j k l : α} (hij : i ≠ j) (hkl : k ≠ l)
    (h4 : (swap i j * swap k l) ^ 4 = 1) : swap i j * swap k l = swap k l * swap i j := by
  rcases swap_pair_trichotomy hij hkl with h | ⟨_, h⟩ | ⟨hnc, h3⟩
  · rw [h]
  · exact h
  · exfalso
    have h1 : swap i j * swap k l = 1 := by
      have : (swap i j * swap k l) ^ 4 = (swap i j * swap k l) ^ 3 * (swap i j * swap k l) := by
        rw [pow_succ]
      rwa [this, h3, one_mul] at h4
    apply hnc
    have e : swap i j = swap k l := by
      have := congrArg (fun p : Perm α => p * swap k l) h1
      simpa [mul_assoc] using this
    rw [e]

end SwapLemmas

section Matching

theorem two_mul_card_le_of_commute {n : ℕ} (S : Finset (Perm (Fin n)))
    (hS : ∀ s ∈ S, ∃ i j, i ≠ j ∧ s = swap i j) (hc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    2 * S.card ≤ n := by
  classical
  have hsupp : ∀ s ∈ S, s.support.card = 2 := fun s hs => by
    obtain ⟨i, j, hij, rfl⟩ := hS s hs
    rw [Perm.support_swap hij]
    exact Finset.card_pair hij
  have hdisj : (S : Set (Perm (Fin n))).PairwiseDisjoint Perm.support := by
    intro s hs t ht hst
    obtain ⟨i, j, hij, rfl⟩ := hS s hs
    obtain ⟨k, l, hkl, rfl⟩ := hS t ht
    rcases swap_pair_trichotomy hij hkl with h | ⟨⟨h1, h2, h3, h4⟩, _⟩ | ⟨hnc, _⟩
    · exact absurd h hst
    · rw [Function.onFun, Perm.support_swap hij, Perm.support_swap hkl]
      simp [Finset.disjoint_left, h1, h2, h3, h4]
    · exact absurd (hc _ hs _ ht) hnc
  have h1 := Finset.card_biUnion hdisj
  rw [Finset.sum_congr rfl hsupp] at h1
  have hle : (S.biUnion Perm.support).card ≤ n := by
    calc _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  simp only [Finset.sum_const, smul_eq_mul] at h1
  omega

theorem exists_swap_matching {n m : ℕ} (hn : n = 2 * m + 1) (E : Fin n → Fin n → Prop)
    (hno3 : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → E i j ∨ E j k ∨ E i k) :
    ∃ S : Finset (Perm (Fin n)), S.card = m ∧
      (∀ s ∈ S, ∃ i j, i ≠ j ∧ E i j ∧ s = swap i j) ∧ ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
  classical
  let P : Finset (Perm (Fin n)) → Prop := fun S =>
    (∀ s ∈ S, ∃ i j, i ≠ j ∧ E i j ∧ s = swap i j) ∧
      ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s.support t.support
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card
    ⟨∅, by simp [P]⟩
  rw [Finset.mem_filter] at hS
  obtain ⟨hSsw, hSdisj⟩ := hS.2
  have hsupp : ∀ s ∈ S, s.support.card = 2 := fun s hs => by
    obtain ⟨i, j, hij, _, rfl⟩ := hSsw s hs
    rw [Perm.support_swap hij]
    exact Finset.card_pair hij
  have hcov : (S.biUnion Perm.support).card = 2 * S.card := by
    rw [Finset.card_biUnion (fun s hs t ht hst => hSdisj s hs t ht hst),
      Finset.sum_congr rfl hsupp, Finset.sum_const, smul_eq_mul, mul_comm]
  have hle : (S.biUnion Perm.support).card ≤ n := by
    calc _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  set U := Finset.univ \ S.biUnion Perm.support with hU
  have hUcard : U.card = n - 2 * S.card := by
    rw [hU, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hcov]
  have hindep : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ¬ E x y := by
    intro x hx y hy hxy hE
    have hxc : x ∉ S.biUnion Perm.support := (Finset.mem_sdiff.1 hx).2
    have hyc : y ∉ S.biUnion Perm.support := (Finset.mem_sdiff.1 hy).2
    have hx' : ∀ t ∈ S, x ∉ t.support := fun t ht hxt =>
      hxc (Finset.mem_biUnion.2 ⟨t, ht, hxt⟩)
    have hy' : ∀ t ∈ S, y ∉ t.support := fun t ht hyt =>
      hyc (Finset.mem_biUnion.2 ⟨t, ht, hyt⟩)
    have hnot : swap x y ∉ S := by
      intro hin
      apply hx' _ hin
      rw [Perm.support_swap hxy]
      simp
    have hdis : ∀ t ∈ S, Disjoint (swap x y).support t.support := by
      intro t ht
      rw [Perm.support_swap hxy, Finset.disjoint_left]
      intro z hz hzt
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hx' t ht hzt
      · rw [Finset.mem_singleton] at hz
        subst hz
        exact hy' t ht hzt
    have hP' : P (insert (swap x y) S) := by
      refine ⟨?_, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact ⟨x, y, hxy, hE, rfl⟩
        · exact hSsw s hs
      · intro s hs t ht hst
        rcases Finset.mem_insert.1 hs with rfl | hs <;> rcases Finset.mem_insert.1 ht with rfl | ht
        · exact absurd rfl hst
        · exact hdis t ht
        · exact (hdis s hs).symm
        · exact hSdisj s hs t ht hst
    have := hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP'⟩)
    rw [Finset.card_insert_of_notMem hnot] at this
    omega
  have hU2 : U.card ≤ 2 := by
    by_contra hgt
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (not_le.1 hgt)
    rcases hno3 a b c hab hbc hac with h | h | h
    · exact hindep a ha b hb hab h
    · exact hindep b hb c hc hbc h
    · exact hindep a ha c hc hac h
  refine ⟨S, ?_, hSsw, ?_⟩
  · omega
  · intro s hs t ht
    by_cases hst : s = t
    · rw [hst]
    · exact (Perm.disjoint_iff_disjoint_support.2 (hSdisj s hs t ht hst)).commute

end Matching

section TwoGroups

variable {G : Type*} [Group G]

theorem closure_mul_comm {C : Set G} (hc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) {x y : G}
    (hx : x ∈ Subgroup.closure C) (hy : y ∈ Subgroup.closure C) : x * y = y * x := by
  have := Subgroup.isMulCommutative_closure (k := C) fun a ha b hb _ => hc a ha b hb
  exact setLike_mul_comm hx hy

theorem mul_self_eq_one_of_mem_closure {C : Set G} (hinv : ∀ x ∈ C, x * x = 1)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) {a : G} (ha : a ∈ Subgroup.closure C) :
    a * a = 1 := by
  induction ha using Subgroup.closure_induction with
  | mem t ht => exact hinv t ht
  | one => exact mul_one 1
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := closure_mul_comm hc ha hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = a * a * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]

theorem isPGroup_closure_of_commuting_involutions {C : Set G} (hinv : ∀ x ∈ C, x * x = 1)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) : IsPGroup 2 (Subgroup.closure C) := by
  intro g
  refine ⟨1, ?_⟩
  have := mul_self_eq_one_of_mem_closure hinv hc g.2
  rw [pow_one, pow_two]
  exact Subtype.ext this

theorem isPGroup_closure_pair_of_dihedral {d e : G} (hd : d * d = 1) (he : e * e = 1)
    (h4 : (d * e) ^ 4 = 1) : IsPGroup 2 (Subgroup.closure {d, e}) := by
  have hd1 : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have he1 : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hH : IsPGroup 2 (Subgroup.zpowers (d * e)) := by
    refine IsPGroup.of_card_dvd_pow (n := 2) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one h4
  have hK : IsPGroup 2 (Subgroup.zpowers d) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hd)
  have hconj : d * (d * e) * d⁻¹ = (d * e)⁻¹ := by
    rw [hd1, mul_inv_rev, he1, hd1]
    calc d * (d * e) * d = (d * d) * e * d := by group
      _ = e * d := by rw [hd, one_mul]
  have hmem : ∀ h ∈ Subgroup.zpowers (d * e), d * h * d⁻¹ ∈ Subgroup.zpowers (d * e) := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have h1 : d * (d * e) ^ k * d⁻¹ = (d * (d * e) * d⁻¹) ^ k := by
      have := map_zpow (MulAut.conj d) (d * e) k
      simpa only [MulAut.conj_apply] using this
    rw [h1, hconj]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) _
  have hKN : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers (d * e)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hmem x, fun hx => ?_⟩
    have := hmem _ hx
    have hx' : d * (d * x * d⁻¹) * d⁻¹ = x := by
      rw [hd1]
      calc d * (d * x * d) * d = (d * d) * x * (d * d) := by group
        _ = x := by rw [hd, one_mul, mul_one]
    rwa [hx'] at this
  have hsup := IsPGroup.to_sup_of_normal_left' hH hK hKN
  refine hsup.to_le ?_
  rw [Subgroup.closure_le]
  rintro x (hx | hx)
  · rw [hx]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have h3 : d * (d * e) ∈ Subgroup.zpowers (d * e) ⊔ Subgroup.zpowers d :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have h4' : d * (d * e) = e := by rw [← mul_assoc, hd, one_mul]
    rwa [h4'] at h3

end TwoGroups

end CFSG.CGT.PushingUpLit.CGT6
