module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutOrder8Hom
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

private lemma orderOf_dvd_two_of_ne_four_ne_eight {G : Type*} [Group G] {x : G}
    (hdvd : orderOf x ∣ 8) (h4 : orderOf x ≠ 4) (h8 : orderOf x ≠ 8) :
    orderOf x ∣ 2 := by
  have h2 : orderOf x ∣ 2 ^ 3 := by simpa using hdvd
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  interval_cases k
  · rw [hk]; norm_num
  · rw [hk]; norm_num
  · exact absurd (by rw [hk]; norm_num : orderOf x = 4) h4
  · exact absurd (by rw [hk]; norm_num : orderOf x = 8) h8

private lemma exists_orderOf_eq_four_of_card_eight {G : Type*} [Group G] [Finite G]
    (h8 : Nat.card G = 8) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∃ a : G, orderOf a = 4 := by
  by_contra hno
  push Not at hno
  have hnotcomm : ¬ IsMulCommutative G := by
    intro hcomm
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (hcomm.is_comm.comm x y)
  have hdvd8 : ∀ x : G, orderOf x ∣ 8 := fun x => by
    rw [← h8]; exact orderOf_dvd_natCard x
  have hno8 : ∀ x : G, orderOf x ≠ 8 := by
    intro x hx8
    have hcyc : IsCyclic G := isCyclic_of_orderOf_eq_card x (hx8.trans h8.symm)
    exact hnotcomm hcyc.isMulCommutative
  have hsq : ∀ x : G, x ^ 2 = 1 := by
    intro x
    have h2 : orderOf x ∣ 2 := orderOf_dvd_two_of_ne_four_ne_eight (hdvd8 x) (hno x) (hno8 x)
    rwa [orderOf_dvd_iff_pow_eq_one] at h2
  have hcommul : ∀ x y : G, x * y = y * x := by
    intro x y
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq x)
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq y)
    have hxy : (x * y)⁻¹ = x * y :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq (x * y))
    rw [← hxy, mul_inv_rev, hx, hy]
  exact hnotcomm ⟨⟨hcommul⟩⟩

private lemma mem_zpowers_eq_pow_of_order_four {G : Type*} [Group G] {a c : G}
    (ha4 : a ^ 4 = 1) (ha2 : a ^ 2 ≠ 1) (hcA : c ∈ Subgroup.zpowers a) :
    c = 1 ∨ c = a ∨ c = a ^ 2 ∨ c = a ^ 3 := by
  have horder : orderOf a = 4 := orderOf_eq_four ha4 ha2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcA
  have hmod : a ^ (k % 4) = c := by
    rw [← hk, ← zpow_mod_orderOf a k]
    rw [show (orderOf a : ℤ) = 4 by rw [horder]; norm_num]
  have hk4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
    have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
    have h3 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rcases hk4 with h | h | h | h
  · left; rw [h] at hmod; simpa using hmod.symm
  · right; left; rw [h] at hmod; simpa using hmod.symm
  · right; right; left; rw [h] at hmod; simpa using hmod.symm
  · right; right; right; rw [h] at hmod; simpa using hmod.symm

private lemma isMulCommutative_of_index_two_conj_eq {G : Type*} [Group G]
    {A : Subgroup G} {a b : G} (hA : A = Subgroup.zpowers a) (hindex : A.index = 2)
    (hbA : b ∉ A) (hconj : b * a * b⁻¹ = a) : IsMulCommutative G := by
  have hbAcomm : ∀ m ∈ A, b * m = m * b := by
    intro m hm
    rw [hA] at hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    have h1 : b * a ^ k * b⁻¹ = a ^ k := by
      rw [← conj_zpow (a := b) (b := a) (i := k), hconj]
    have h2 : b * a ^ k = a ^ k * b := by
      calc b * a ^ k = b * a ^ k * b⁻¹ * b := by group
        _ = a ^ k * b := by rw [h1]
    rw [← hk]
    exact h2
  have hbAcomm' : ∀ m ∈ A, b⁻¹ * m = m * b⁻¹ := by
    intro m hm
    have h : Commute b m := hbAcomm m hm
    exact h.inv_left.eq
  have hAcomm : ∀ m ∈ A, ∀ n ∈ A, m * n = n * m := by
    intro m hm n hn
    rw [hA] at hm hn
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← zpow_add, ← zpow_add, add_comm]
  have hrepr : ∀ x : G, ∃ m ∈ A, x = m ∨ x = m * b⁻¹ := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨x, hx, Or.inl rfl⟩
    · refine ⟨x * b, ?_, Or.inr ?_⟩
      · rw [Subgroup.mul_mem_iff_of_index_two hindex]
        exact ⟨fun h => absurd h hx, fun h => absurd h hbA⟩
      · group
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨m, hmA, hm⟩ := hrepr x
  obtain ⟨n, hnA, hn⟩ := hrepr y
  rcases hm with hm | hm <;> rcases hn with hn | hn
  · rw [hm, hn]
    exact hAcomm m hmA n hnA
  · rw [hm, hn]
    calc m * (n * b⁻¹) = m * n * b⁻¹ := by group
      _ = n * m * b⁻¹ := by rw [hAcomm m hmA n hnA]
      _ = n * (m * b⁻¹) := by group
      _ = n * (b⁻¹ * m) := by rw [← hbAcomm' m hmA]
      _ = (n * b⁻¹) * m := by group
  · rw [hm, hn]
    calc (m * b⁻¹) * n = m * (b⁻¹ * n) := by group
      _ = m * (n * b⁻¹) := by rw [hbAcomm' n hnA]
      _ = m * n * b⁻¹ := by group
      _ = n * m * b⁻¹ := by rw [hAcomm m hmA n hnA]
      _ = n * (m * b⁻¹) := by group
  · rw [hm, hn]
    calc (m * b⁻¹) * (n * b⁻¹) = m * (b⁻¹ * n) * b⁻¹ := by group
      _ = m * (n * b⁻¹) * b⁻¹ := by rw [hbAcomm' n hnA]
      _ = m * n * b⁻¹ * b⁻¹ := by group
      _ = n * m * b⁻¹ * b⁻¹ := by rw [hAcomm m hmA n hnA]
      _ = n * (m * b⁻¹) * b⁻¹ := by group
      _ = n * (b⁻¹ * m) * b⁻¹ := by rw [← hbAcomm' m hmA]
      _ = (n * b⁻¹) * (m * b⁻¹) := by group

theorem order8_nonabelian {G : Type} [Group G] [Finite G] (h8 : Nat.card G = 8)
    (hnab : ∃ a b : G, a * b ≠ b * a) :
    Nonempty (G ≃* DihedralGroup 4) ∨ Nonempty (G ≃* QuaternionGroup 2) := by
  have hnotcomm : ¬ IsMulCommutative G := by
    intro hcomm
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (hcomm.is_comm.comm x y)
  obtain ⟨a, ha_order⟩ := exists_orderOf_eq_four_of_card_eight h8 hnab
  have ha4 : a ^ 4 = 1 := by rw [← ha_order]; exact pow_orderOf_eq_one a
  have ha2 : a ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [ha_order] at hdvd
    norm_num at hdvd
  let A : Subgroup G := Subgroup.zpowers a
  have hAcard : Nat.card A = 4 := by
    show Nat.card (Subgroup.zpowers a) = 4
    rw [Nat.card_zpowers, ha_order]
  have hindex : A.index = 2 := by
    have hmul := A.card_mul_index
    rw [hAcard, h8] at hmul
    omega
  have hAnormal : A.Normal := Subgroup.normal_of_index_eq_two hindex
  have hproper : A ≠ ⊤ := by
    intro htop
    have hcardtop : Nat.card A = Nat.card G := by
      rw [htop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    omega
  obtain ⟨b, hbA⟩ : ∃ b : G, b ∉ A := by
    by_contra h
    push Not at h
    exact hproper (le_antisymm le_top (fun x _ => h x))
  have hconjmem : b * a * b⁻¹ ∈ A := hAnormal.conj_mem a (Subgroup.mem_zpowers a) b
  have hc4 : orderOf (b * a * b⁻¹) = 4 := by
    have hsc : SemiconjBy b a (b * a * b⁻¹) := by
      rw [SemiconjBy]
      group
    exact (SemiconjBy.orderOf_eq b hsc).symm.trans ha_order
  have hbab : b * a * b⁻¹ = a⁻¹ := by
    have hpow := mem_zpowers_eq_pow_of_order_four ha4 ha2 hconjmem
    rcases hpow with h | h | h | h
    · exfalso
      rw [h] at hc4
      simp at hc4
    · exfalso
      exact hnotcomm (isMulCommutative_of_index_two_conj_eq rfl hindex hbA h)
    · exfalso
      rw [h] at hc4
      have hdvd : orderOf (a ^ 2) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, show 2 * 2 = 4 by norm_num, ha4])
      have hle : orderOf (a ^ 2) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · rw [h, eq_inv_iff_mul_eq_one]
      rw [show a ^ 3 * a = a ^ 4 by rw [← pow_succ]]
      exact ha4
  have hb2A : b * b ∈ A := by
    simpa [pow_two] using Subgroup.sq_mem_of_index_two hindex b
  have hb2 : b * b = 1 ∨ b * b = a ^ 2 := by
    have hpow := mem_zpowers_eq_pow_of_order_four ha4 ha2 hb2A
    rcases hpow with h | h | h | h
    · exact Or.inl h
    · exfalso
      have hconj' : b * a * b⁻¹ = a := by
        rw [← h]
        group
      rw [hconj'] at hbab
      have h2 : a ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [hbab]
        rw [inv_mul_cancel]
      exact ha2 h2
    · exact Or.inr h
    · exfalso
      have h1 : b * a ^ 3 * b⁻¹ = a ^ 3 := by
        rw [← h]
        group
      have h2 : b * a ^ 3 * b⁻¹ = (a ^ 3)⁻¹ := by
        rw [← conj_pow (a := b) (b := a) (i := 3), hbab, inv_pow]
      have ha3eq : a ^ 3 = (a ^ 3)⁻¹ := by
        rw [h1] at h2
        exact h2
      have h6 : (a ^ 3) ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [ha3eq]
        rw [mul_inv_cancel]
      have h26 : (a ^ 3) ^ 2 = a ^ 2 := by
        rw [← pow_mul, show 3 * 2 = 6 by norm_num,
          show (6 : ℕ) = 4 + 2 by norm_num, pow_add, ha4, one_mul]
      exact ha2 (h26 ▸ h6)
  rcases hb2 with hb2 | hb2
  · left
    obtain ⟨φ, hφinj, -, -⟩ :=
      exists_dihedral_hom a b ha4 ha2 (by rw [pow_two]; exact hb2) hbab
    have hbij : Function.Bijective φ :=
      hφinj.bijective_of_nat_card_le (by rw [h8, DihedralGroup.nat_card])
    exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩
  · right
    obtain ⟨φ, hφinj, -, -⟩ :=
      exists_quaternion_hom a b ha4 ha2 (by rw [pow_two]; exact hb2) hbab
    have hbij : Function.Bijective φ :=
      hφinj.bijective_of_nat_card_le (by
        rw [h8, Nat.card_eq_fintype_card, QuaternionGroup.card])
    exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
