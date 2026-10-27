module

public import CFSG.GroupTheory.ThompsonIndexTwo
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Prime.Int

public section

namespace CFSG.CGT.T75H

variable {G : Type} [Group G]

theorem exists_index_two_of_cyclic_factor [Finite G] {S A : Subgroup G} (hS : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.index) (hAS : A ≤ S) {c : G} (hcS : c ∈ S) (hc1 : c ≠ 1)
    (hdec : ∀ s ∈ S, ∃ d ∈ A, ∃ j : ℤ, s = d * c ^ j)
    (hinf : ∀ d ∈ A, ∀ j : ℤ, d * c ^ j = 1 → d = 1 ∧ c ^ j = 1)
    (hcomm : ∀ d ∈ A, d * c = c * d)
    (hfuse : ∀ g : G, ∀ z ∈ A, g⁻¹ * c ^ (orderOf c / 2) * g ≠ z) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨c, hcS⟩
  have hk' : orderOf c = 2 ^ k := (Subgroup.orderOf_coe (⟨c, hcS⟩ : S)).trans hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (orderOf_eq_one_iff.1 (by simpa using hk')) hc1
    · exact h
  have h2n : 2 ∣ orderOf c := by
    rw [hk']
    exact dvd_pow_self 2 (by omega)
  have hcz : ∀ d ∈ A, ∀ m : ℤ, d * c ^ m = c ^ m * d := fun d hd m =>
    ((Commute.zpow_right (show Commute d c from hcomm d hd) m)).eq
  let U : Subgroup G :=
    { carrier := {y | ∃ d ∈ A, ∃ i : ℤ, y = d * c ^ (2 * i)}
      mul_mem' := by
        rintro _ _ ⟨d, hd, i, rfl⟩ ⟨d', hd', i', rfl⟩
        refine ⟨d * d', A.mul_mem hd hd', i + i', ?_⟩
        calc d * c ^ (2 * i) * (d' * c ^ (2 * i')) = d * (c ^ (2 * i) * d') * c ^ (2 * i') := by
              group
          _ = d * (d' * c ^ (2 * i)) * c ^ (2 * i') := by rw [← hcz d' hd']
          _ = d * d' * (c ^ (2 * i) * c ^ (2 * i')) := by group
          _ = d * d' * c ^ (2 * (i + i')) := by rw [← zpow_add]; ring_nf
      one_mem' := ⟨1, A.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨d, hd, i, rfl⟩
        refine ⟨d⁻¹, A.inv_mem hd, -i, ?_⟩
        calc (d * c ^ (2 * i))⁻¹ = (c ^ (2 * i))⁻¹ * d⁻¹ := by group
          _ = d⁻¹ * (c ^ (2 * i))⁻¹ := by
              rw [← zpow_neg, ← hcz d⁻¹ (A.inv_mem hd)]
          _ = d⁻¹ * c ^ (2 * -i) := by rw [← zpow_neg]; ring_nf }
  have hUmem : ∀ y, y ∈ U ↔ ∃ d ∈ A, ∃ i : ℤ, y = d * c ^ (2 * i) := fun y => Iff.rfl
  have hUS : U ≤ S := by
    rintro _ ⟨d, hd, i, rfl⟩
    exact S.mul_mem (hAS hd) (S.zpow_mem hcS _)
  have hmemU : ∀ d ∈ A, ∀ j : ℤ, d * c ^ j ∈ U ↔ (2 : ℤ) ∣ j := by
    intro d hd j
    constructor
    · rintro ⟨d', hd', i, h⟩
      have h1 : (d'⁻¹ * d) * c ^ (j - 2 * i) = 1 := by
        calc (d'⁻¹ * d) * c ^ (j - 2 * i) = d'⁻¹ * (d * c ^ j) * c ^ (-(2 * i)) := by
              rw [sub_eq_add_neg, zpow_add]; group
          _ = d'⁻¹ * (d' * c ^ (2 * i)) * c ^ (-(2 * i)) := by rw [h]
          _ = 1 := by
              rw [zpow_neg]; group
      have h2 := (hinf _ (A.mul_mem (A.inv_mem hd') hd) _ h1).2
      have h3 : (orderOf c : ℤ) ∣ j - 2 * i := orderOf_dvd_iff_zpow_eq_one.2 h2
      obtain ⟨m, hm⟩ := h2n
      have h4 : ((2 * m : ℕ) : ℤ) ∣ j - 2 * i := by rw [← hm]; exact h3
      obtain ⟨r, hr⟩ := h4
      push_cast at hr
      exact ⟨i + m * r, by linarith⟩
    · rintro ⟨i, rfl⟩
      exact ⟨d, hd, i, rfl⟩
  have hcU : c ∉ U := by
    intro h
    have h' : (1 : G) * c ^ (1 : ℤ) ∈ U := by simpa using h
    rw [hmemU 1 A.one_mem] at h'
    omega
  have hrel : U.relIndex S = 2 := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨c, hcS⟩, ?_⟩
    rintro ⟨s, hs⟩
    obtain ⟨d, hd, j, rfl⟩ := hdec s hs
    have h1 : (⟨d * c ^ j, hs⟩ * ⟨c, hcS⟩ : S) ∈ U.subgroupOf S ↔ (2 : ℤ) ∣ j + 1 := by
      rw [Subgroup.mem_subgroupOf]
      show d * c ^ j * c ∈ U ↔ _
      rw [show d * c ^ j * c = d * c ^ (j + 1) by rw [zpow_add_one]; group]
      exact hmemU d hd (j + 1)
    have h2 : (⟨d * c ^ j, hs⟩ : S) ∈ U.subgroupOf S ↔ (2 : ℤ) ∣ j := by
      rw [Subgroup.mem_subgroupOf]
      exact hmemU d hd j
    rw [h1, h2]
    by_cases hj : (2 : ℤ) ∣ j
    · right
      exact ⟨hj, by omega⟩
    · left
      exact ⟨by omega, hj⟩
  have hmin : ∀ y ∈ S, y ∉ U → orderOf c ≤ orderOf y := by
    intro y hy hyU
    obtain ⟨d, hd, j, rfl⟩ := hdec y hy
    have hj : ¬ (2 : ℤ) ∣ j := fun h => hyU ((hmemU d hd j).2 h)
    have hmpos : 0 < orderOf (d * c ^ j) := orderOf_pos _
    have hpow : (d * c ^ j) ^ orderOf (d * c ^ j) = 1 := pow_orderOf_eq_one _
    have hcommdc : Commute d (c ^ j) := Commute.zpow_right (show Commute d c from hcomm d hd) j
    have h3 : (c ^ j) ^ orderOf (d * c ^ j) = c ^ (j * (orderOf (d * c ^ j) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul]
    have hpow' : d ^ orderOf (d * c ^ j) * c ^ (j * (orderOf (d * c ^ j) : ℤ)) = 1 := by
      rw [← h3, ← hcommdc.mul_pow]; exact hpow
    have h4 := (hinf _ (A.pow_mem hd _) _ hpow').2
    have h5 : (orderOf c : ℤ) ∣ j * (orderOf (d * c ^ j) : ℤ) := orderOf_dvd_iff_zpow_eq_one.2 h4
    have hcop : IsCoprime ((2 : ℤ) ^ k) j :=
      ((Int.prime_two.irreducible.coprime_iff_not_dvd).2 hj).pow_left
    rw [hk'] at h5 ⊢
    have h6 : ((2 : ℤ) ^ k) ∣ (orderOf (d * c ^ j) : ℤ) := by
      have h5' : ((2 ^ k : ℕ) : ℤ) ∣ j * (orderOf (d * c ^ j) : ℤ) := h5
      push_cast at h5'
      exact hcop.dvd_of_dvd_mul_left h5'
    have h7 := Int.le_of_dvd (by exact_mod_cast hmpos) h6
    exact_mod_cast h7
  have hconj : ∀ g : G, g⁻¹ * c * g ∉ U := by
    intro g hg
    obtain ⟨d, hd, i, hdi⟩ := hg
    have e1 : (g⁻¹ * c * g) ^ (orderOf c / 2) = g⁻¹ * c ^ (orderOf c / 2) * g := by
      have := conj_pow (a := g⁻¹) (b := c) (i := orderOf c / 2)
      simpa using this
    obtain ⟨n2, hn2⟩ := h2n
    have hdiv : orderOf c / 2 = n2 := by omega
    have e2 : (d * c ^ (2 * i)) ^ (orderOf c / 2) = d ^ (orderOf c / 2) := by
      have hcc : Commute d (c ^ (2 * i)) :=
        Commute.zpow_right (show Commute d c from hcomm d hd) (2 * i)
      rw [hcc.mul_pow]
      have : (c ^ (2 * i)) ^ (orderOf c / 2) = 1 := by
        rw [← zpow_natCast, ← zpow_mul]
        have : 2 * i * ((orderOf c / 2 : ℕ) : ℤ) = (orderOf c : ℤ) * i := by
          rw [hdiv, hn2]
          push_cast
          ring
        rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
      rw [this, mul_one]
    exact hfuse g (d ^ (orderOf c / 2)) (A.pow_mem hd _) (by rw [← e1, hdi, e2])
  exact CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hS hSidx hUS hrel hcS hcU hmin
    hconj

end CFSG.CGT.T75H
