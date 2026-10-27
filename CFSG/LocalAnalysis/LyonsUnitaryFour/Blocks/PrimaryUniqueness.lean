module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.PrimaryParts

public section

namespace CFSG.LyonsUnitaryFour

theorem factors_mem_zpowers_of_coprime {G : Type*} [Group G] {a b : G} (hab : Commute a b)
    (hcop : Nat.Coprime (orderOf a) (orderOf b)) :
    a ∈ Subgroup.zpowers (a * b) ∧ b ∈ Subgroup.zpowers (a * b) := by
  obtain ⟨k, hk⟩ := CFSG.BlockSectionOrthogonality.Helpers.primaryPart_eq_power_of_coprime_factors
    (rfl : a * b = a * b) hab hcop
  obtain ⟨l, hl⟩ := CFSG.BlockSectionOrthogonality.Helpers.primaryPart_eq_power_of_coprime_factors
    (hab.eq.symm : b * a = a * b) hab.symm hcop.symm
  refine ⟨⟨k, ?_⟩, ⟨l, ?_⟩⟩
  · simpa using hk
  · simpa using hl

theorem primary_factorization_unique {G : Type*} [Group G] {p : ℕ} {a b a' b' : G} {k k' : ℕ}
    (ha : orderOf a ∣ p ^ k) (hb : Nat.Coprime p (orderOf b)) (hab : Commute a b)
    (ha' : orderOf a' ∣ p ^ k') (hb' : Nat.Coprime p (orderOf b')) (hab' : Commute a' b')
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have hcop : Nat.Coprime (orderOf a) (orderOf b) := (hb.pow_left k).of_dvd_left ha
  have hcop' : Nat.Coprime (orderOf a') (orderOf b') := (hb'.pow_left k').of_dvd_left ha'
  obtain ⟨haw, hbw⟩ := factors_mem_zpowers_of_coprime hab hcop
  obtain ⟨haw', hbw'⟩ := factors_mem_zpowers_of_coprime hab' hcop'
  rw [← h] at haw' hbw'
  have hcomm : ∀ x ∈ Subgroup.zpowers (a * b), ∀ y ∈ Subgroup.zpowers (a * b), Commute x y := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow_self _ i j
  set z := a'⁻¹ * a with hz
  have hz' : z = b' * b⁻¹ := by
    rw [hz]
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hzp : orderOf z ∣ p ^ (k' + k) := by
    rw [hz, pow_add]
    refine ((hcomm _ (Subgroup.inv_mem _ haw') _ haw).orderOf_mul_dvd_mul_orderOf).trans ?_
    rw [orderOf_inv]
    exact Nat.mul_dvd_mul ha' ha
  have hzq : Nat.Coprime p (orderOf z) := by
    rw [hz']
    apply Nat.Coprime.coprime_dvd_right
      ((hcomm _ hbw' _ (Subgroup.inv_mem _ hbw)).orderOf_mul_dvd_mul_orderOf)
    rw [orderOf_inv]
    exact Nat.Coprime.mul_right hb' hb
  have hz1 : z = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.Coprime.eq_one_of_dvd ((hzq.pow_left (k' + k)).symm) hzp
  have haa' : a = a' := by
    rw [hz] at hz1
    exact (inv_mul_eq_one.mp hz1).symm
  refine ⟨haa', ?_⟩
  rw [haa'] at h
  exact mul_left_cancel h

end CFSG.LyonsUnitaryFour
