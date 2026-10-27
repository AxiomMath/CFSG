module

public import CFSG.GH74.GLS.C3.Prop121.CentralQuot
public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm Subgroup CFSG.GH74.GLS

theorem alt9_no_order_eight (σ : Perm (Fin 9)) (hs : sign σ = 1) : orderOf σ ≠ 8 := by
  intro h8
  have hl := lcm_cycleType σ
  rw [h8] at hl
  have hmem : ∀ n ∈ σ.cycleType, 2 ≤ n := fun n hn => two_le_of_mem_cycleType hn
  have hdvd : ∀ n ∈ σ.cycleType, n ∣ 8 := fun n hn => hl ▸ Multiset.dvd_lcm hn
  have h8mem : 8 ∈ σ.cycleType := by
    by_contra hno
    have h4 : σ.cycleType.lcm ∣ 4 := by
      apply Multiset.lcm_dvd.2
      intro n hn
      have h1 := hdvd n hn
      have h2 := hmem n hn
      have h3 : n ≠ 8 := fun h => hno (h ▸ hn)
      have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) h1
      interval_cases n <;> omega
    rw [hl] at h4
    omega
  have hsum : σ.cycleType.sum ≤ 9 := by
    rw [sum_cycleType]
    calc σ.support.card ≤ Fintype.card (Fin 9) := Finset.card_le_univ _
      _ = 9 := by simp
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem h8mem
  have hrest0 : rest = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne
    have h2 : 2 ≤ y := hmem y (by rw [hrest]; exact Multiset.mem_cons_of_mem hy)
    have hle : y ≤ rest.sum := Multiset.le_sum_of_mem hy
    rw [hrest, Multiset.sum_cons] at hsum
    omega
  have hct : σ.cycleType = {8} := by rw [hrest, hrest0]; rfl
  have := sign_of_cycleType σ
  rw [hct, hs] at this
  simp at this
  revert this
  decide

theorem no_order_eight_of_approx_nine {G : Type} [Group G] [Finite G]
    (hA : IsApproxTo G (alternatingGroup (Fin 9))) : ∀ m : G, ¬ 8 ∣ orderOf m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, S', φ, -, -⟩ := hA.1
  intro m hm
  have ho : orderOf m ≠ 0 := (orderOf_pos m).ne'
  have hm'8 : orderOf (m ^ (orderOf m / 8)) = 8 := orderOf_pow_orderOf_div ho hm
  set m' := m ^ (orderOf m / 8) with hm'
  have hpg : IsPGroup 2 (Subgroup.zpowers m') :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, hm'8]; norm_num)
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S Q
  have hmQ : m' ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers m')
  rw [← hh, mem_smul_sylow_iff] at hmQ
  let y : ↥(S : Subgroup G) := ⟨h⁻¹ * m' * h, hmQ⟩
  have hy : orderOf y = 8 := by
    rw [← Subgroup.orderOf_coe]
    show orderOf (h⁻¹ * m' * h) = 8
    have : h⁻¹ * m' * h = (MulAut.conj h⁻¹) m' := by simp
    rw [this, MulEquiv.orderOf_eq, hm'8]
  have hy' : orderOf (φ y) = 8 := by rw [MulEquiv.orderOf_eq, hy]
  have hz : orderOf ((φ y : ↥S') : alternatingGroup (Fin 9)) = 8 := by
    rw [Subgroup.orderOf_coe]; exact hy'
  have hz2 : orderOf (((φ y : ↥S') : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 8 := by
    rw [Subgroup.orderOf_coe]; exact hz
  exact alt9_no_order_eight _ (mem_alternatingGroup.1 ((φ y : ↥S') : alternatingGroup (Fin 9)).2) hz2

theorem false_of_transvection {G : Type*} [Group G] [Finite G] (hno8 : ∀ m : G, ¬ 8 ∣ orderOf m)
    {a b g c : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hg2 : g * g = 1) (hga : g * a * g⁻¹ = b) (hca : c * a * c⁻¹ = a) {k : ℤ}
    (hk : k = 1 ∨ k = -1) (hcb : c * b * c⁻¹ = b * a ^ k) : False := by
  have hg1 : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hg2, inv_one]
  have hgb : g * b * g⁻¹ = a := by
    rw [← hga]
    calc g * (g * a * g⁻¹) * g⁻¹ = (g * g) * a * (g⁻¹ * g⁻¹) := by group
      _ = a := by rw [hg2, hg1]; group
  set m : G := g * c with hm
  have hma : m * a * m⁻¹ = b := by
    calc m * a * m⁻¹ = g * (c * a * c⁻¹) * g⁻¹ := by rw [hm]; group
      _ = b := by rw [hca, hga]
  have hmb : m * b * m⁻¹ = a * b ^ k := by
    calc m * b * m⁻¹ = g * (c * b * c⁻¹) * g⁻¹ := by rw [hm]; group
      _ = g * (b * a ^ k) * g⁻¹ := by rw [hcb]
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) ^ k := by rw [conj_zpow]; group
      _ = a * b ^ k := by rw [hgb, hga]
  have hba : b * a = a * b := hab.symm
  have hbia : b⁻¹ * a = a * b⁻¹ := (Commute.inv_left (show Commute b a from hba)).eq
  let φ : G ≃* G := MulAut.conj m
  have hφ : ∀ x, φ x = m * x * m⁻¹ := fun x => rfl
  have hφa : φ a = b := by rw [hφ]; exact hma
  have hφb : φ b = a * b ^ k := by rw [hφ]; exact hmb
  have h4 : φ (φ (φ (φ a))) = a ^ 2 := by
    rcases hk with rfl | rfl
    · simp only [zpow_one] at hφb
      simp only [hφa, hφb, map_mul]
      have e1 : b * b * a = a * (b * b) := by rw [mul_assoc, hba, ← mul_assoc, hba, mul_assoc]
      calc a * b * (b * (a * b)) = a * (b * b * a) * b := by group
        _ = a * (a * (b * b)) * b := by rw [e1]
        _ = a * a * (b ^ 3) := by rw [pow_three]; group
        _ = a ^ 2 := by rw [hb3, mul_one, pow_two]
    · simp only [zpow_neg, zpow_one] at hφb
      simp only [hφa, hφb, map_mul, map_inv]
      calc a * b⁻¹ * (b * (a * b⁻¹)⁻¹)⁻¹ = a * (b⁻¹ * a) * b⁻¹ * b⁻¹ := by group
        _ = a * (a * b⁻¹) * b⁻¹ * b⁻¹ := by rw [hbia]
        _ = a * a * (b ^ 3)⁻¹ := by rw [pow_three]; group
        _ = a ^ 2 := by rw [hb3, inv_one, mul_one, pow_two]
  have hm4 : m ^ 4 * a * (m ^ 4)⁻¹ = a ^ 2 := by
    have h5 : (MulAut.conj (m ^ 4)) a = φ (φ (φ (φ a))) := by
      rw [map_pow]
      simp [pow_succ, φ]
    rw [← h4, ← h5]
    rfl
  have hmem4 : ∀ j : ℕ, (m ^ 4) ^ j * a * ((m ^ 4) ^ j)⁻¹ = a ^ (2 ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (m ^ 4) ^ (j + 1) * a * ((m ^ 4) ^ (j + 1))⁻¹ =
          (m ^ 4) * ((m ^ 4) ^ j * a * ((m ^ 4) ^ j)⁻¹) * (m ^ 4)⁻¹ := by group
      rw [e, ih, ← conj_pow, hm4, ← pow_mul, pow_succ, mul_comm]
  obtain ⟨s, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  have hs : s ≤ 2 := by
    by_contra hs
    push Not at hs
    apply hno8 m
    rw [hor]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 hs : 2 ^ 3 ∣ 2 ^ s) r
  have hdvd : orderOf m ∣ 4 * r := by
    rw [hor]
    have : 2 ^ s ∣ 4 := by
      have h4' : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4']; exact pow_dvd_pow 2 hs
    exact Nat.mul_dvd_mul_right this r
  have hm4r : m ^ (4 * r) = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
  have h1 : (m ^ 4) ^ r = 1 := by rw [← pow_mul]; exact hm4r
  have h2 := hmem4 r
  rw [h1] at h2
  simp only [one_mul, inv_one, mul_one] at h2
  have h3 : a ^ (2 ^ r) = a ^ 2 := by
    rw [pow_eq_pow_mod (2 ^ r) ha3, pow_eq_pow_mod 2 ha3]
    congr 1
    obtain ⟨j, rfl⟩ := hr
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [h3] at h2
  apply ha1
  have : a * a = a * 1 := by rw [mul_one, ← pow_two]; exact h2.symm
  exact mul_left_cancel this

end CFSG.GH74.GLS.C3.Prop121
