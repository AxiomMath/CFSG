module

public import CFSG.GH74.Uniqueness.SU.SU1Arith
public import CFSG.GH74.Uniqueness.SU.SU1CyclicIdx

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

section Shape

variable {P : Type} [Group P] [Finite P]

theorem exists_pow_eq_of_mem_zpowers {a x : P} (hx : x ∈ zpowers a) : ∃ r : ℕ, a ^ r = x := by
  have := (mem_powers_iff_mem_zpowers).mpr hx
  exact (Submonoid.mem_powers_iff x a).mp this

theorem closure_pair_eq_top {a y : P} (hM : (zpowers a).index = 2) (hy : y ∉ zpowers a) :
    Subgroup.closure ({a, y} : Set P) = ⊤ := by
  set K := Subgroup.closure ({a, y} : Set P) with hK
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hyK : y ∈ K := Subgroup.subset_closure (by simp)
  have hMK : zpowers a ≤ K := Subgroup.zpowers_le.mpr haK
  have hlt : zpowers a < K := lt_of_le_of_ne hMK (fun h => hy (h ▸ hyK))
  have hdvd1 : Nat.card (zpowers a) ∣ Nat.card K := Subgroup.card_dvd_of_le hMK
  have hdvd2 : Nat.card K ∣ Nat.card P := Subgroup.card_subgroup_dvd_card K
  have hP : Nat.card P = 2 * Nat.card (zpowers a) := by
    have := Subgroup.card_mul_index (zpowers a)
    rw [hM] at this
    omega
  obtain ⟨c, hc⟩ := hdvd1
  have hpos : 0 < Nat.card (zpowers a) := Nat.card_pos
  rw [hc, hP] at hdvd2
  have hc2 : c ∣ 2 := by
    have : Nat.card (zpowers a) * c ∣ Nat.card (zpowers a) * 2 := by
      rwa [mul_comm 2] at hdvd2
    exact (Nat.mul_dvd_mul_iff_left hpos).mp this
  have hc1 : c ≠ 1 := by
    intro h
    have := Subgroup.card_lt_of_lt hlt
    rw [hc, h, mul_one] at this
    exact lt_irrefl _ this
  have hc2' : c = 2 := ((Nat.dvd_prime Nat.prime_two).mp hc2).resolve_left hc1
  apply Subgroup.eq_top_of_card_eq
  rw [hc, hc2', hP, mul_comm]

theorem exists_conj_pow {a : P} (y : P) (hM : (zpowers a).index = 2) :
    ∃ r : ℕ, y * a * y⁻¹ = a ^ r := by
  have hn : (zpowers a).Normal := Subgroup.normal_of_index_eq_two hM
  have h := hn.conj_mem a (Subgroup.mem_zpowers a) y
  obtain ⟨r, hr⟩ := exists_pow_eq_of_mem_zpowers h
  exact ⟨r, hr.symm⟩

theorem exists_sq_pow {a : P} (y : P) (hM : (zpowers a).index = 2) : ∃ j : ℕ, y * y = a ^ j := by
  have h := Subgroup.mul_self_mem_of_index_two hM y
  obtain ⟨j, hj⟩ := exists_pow_eq_of_mem_zpowers h
  exact ⟨j, hj.symm⟩

theorem conj_exponent_cases {n : ℕ} (hn : 4 ≤ n) {a : P} (ha : orderOf a = 2 ^ (n - 1))
    (hM : (zpowers a).index = 2) (y : P) :
    y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a ^ (2 ^ (n - 2) + 1) ∨ y * a * y⁻¹ = a ^ (2 ^ (n - 2) - 1) ∨
      y * a * y⁻¹ = a⁻¹ := by
  obtain ⟨r, hr⟩ := exists_conj_pow y hM
  obtain ⟨j, hj⟩ := exists_sq_pow y hM
  have ha1 : a ^ (2 ^ (n - 1)) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hsq : a ^ (r * r) = a ^ 1 := by
    have h1 : (y * y) * a * (y * y)⁻¹ = a := by
      rw [hj]
      have hc : Commute (a ^ j) a := (Commute.refl a).pow_left j
      calc a ^ j * a * (a ^ j)⁻¹ = a * a ^ j * (a ^ j)⁻¹ := by rw [hc.eq]
        _ = a := by group
    have h2 : (y * y) * a * (y * y)⁻¹ = a ^ (r * r) := by
      have e : (y * y) * a * (y * y)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ := by group
      rw [e, hr, ← conj_pow, hr, ← pow_mul]
    rw [← h2, h1, pow_one]
  have hmod : r * r % 2 ^ (n - 1) = 1 := by
    have := pow_inj_mod.mp hsq
    rw [ha] at this
    rw [this]
    exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have h4 : 4 * 2 ^ (n - 3) = 2 ^ (n - 1) := by
    have : n - 1 = (n - 3) + 2 := by omega
    rw [this, pow_add]
    ring
  have hq : IsPrimePow (2 ^ (n - 3)) := Nat.prime_two.isPrimePow.pow (by omega)
  have hq2 : 2 ∣ 2 ^ (n - 3) := dvd_pow_self 2 (by omega)
  have hres := sq_mod_eq_one hq hq2 (by rw [h4]; exact hmod)
  have hrr : y * a * y⁻¹ = a ^ (r % 2 ^ (n - 1)) := by
    rw [hr, pow_eq_pow_mod r ha1]
  have e1 : 2 * 2 ^ (n - 3) = 2 ^ (n - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h4, e1] at hres
  rcases hres with h | h | h | h
  · left
    rw [hrr, h, pow_one]
  · right; left
    rw [hrr, h]
  · right; right; left
    rw [hrr, h]
  · right; right; right
    rw [hrr, h]
    apply eq_inv_of_mul_eq_one_left
    have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    rw [← pow_succ, Nat.sub_add_cancel hpos]
    exact ha1

theorem false_of_sq_central {n : ℕ} (hn : 4 ≤ n) {a y : P} (ha : orderOf a = 2 ^ (n - 1))
    (hcl : Subgroup.closure ({a, y} : Set P) = ⊤) (hZ : Nat.card (center P) = 2)
    (hy : y * a ^ 2 * y⁻¹ = a ^ 2) : False := by
  have hcomm_y : y * a ^ 2 = a ^ 2 * y := by
    calc y * a ^ 2 = y * a ^ 2 * y⁻¹ * y := by group
      _ = a ^ 2 * y := by rw [hy]
  have hcent : a ^ 2 ∈ center P := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.closure ({a, y} : Set P) := by rw [hcl]; trivial
    have hle : Subgroup.closure ({a, y} : Set P) ≤ centralizer ({a ^ 2} : Set P) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by group)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm_y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hle : zpowers (a ^ 2) ≤ center P := Subgroup.zpowers_le.mpr hcent
  have h1 := Subgroup.card_le_of_le hle
  have h2 : 2 ∣ orderOf a := by
    rw [ha]
    exact dvd_pow_self 2 (by omega)
  rw [Nat.card_zpowers, hZ, orderOf_pow_of_dvd (by norm_num) h2, ha] at h1
  have h3 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have h4 : 4 ≤ 2 ^ (n - 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right two_pos (by omega)
  rw [h3, Nat.mul_div_cancel_left _ two_pos] at h1
  omega

theorem false_of_exponent_one {n : ℕ} (hn : 4 ≤ n) {a y : P} (ha : orderOf a = 2 ^ (n - 1))
    (hcl : Subgroup.closure ({a, y} : Set P) = ⊤) (hZ : Nat.card (center P) = 2)
    (h : y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a ^ (2 ^ (n - 2) + 1)) : False := by
  have ha1 : a ^ (2 ^ (n - 1)) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  apply false_of_sq_central hn ha hcl hZ
  rw [← conj_pow]
  rcases h with h | h
  · rw [h]
  · rw [h, ← pow_mul]
    have h3 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    have : (2 ^ (n - 2) + 1) * 2 = 2 ^ (n - 1) + 2 := by rw [h3]; ring
    rw [this, pow_add, ha1, one_mul]

omit [Finite P] in
theorem pow_eq_one_or_of_dvd {n : ℕ} (hn : 4 ≤ n) {a : P} (ha : orderOf a = 2 ^ (n - 1)) {j : ℕ}
    (hj : 2 ^ (n - 2) ∣ j) : a ^ j = 1 ∨ a ^ j = a ^ (2 ^ (n - 2)) := by
  obtain ⟨s, rfl⟩ := hj
  have ha1 : a ^ (2 ^ (n - 1)) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb : (a ^ (2 ^ (n - 2))) ^ 2 = 1 := by
    rw [← pow_mul]
    have : 2 ^ (n - 2) * 2 = 2 ^ (n - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this, ha1]
  rcases Nat.even_or_odd' s with ⟨k, rfl | rfl⟩
  · left
    rw [pow_mul, pow_mul, hb, one_pow]
  · right
    rw [pow_mul, pow_succ, pow_mul, hb, one_pow, one_mul]

theorem sq_cases_inv {n : ℕ} (hn : 4 ≤ n) {a y : P} (ha : orderOf a = 2 ^ (n - 1))
    (hM : (zpowers a).index = 2) (hy : y * a * y⁻¹ = a⁻¹) :
    y * y = 1 ∨ y * y = a ^ (2 ^ (n - 2)) := by
  obtain ⟨j, hj⟩ := exists_sq_pow y hM
  have h1 : y * a ^ j * y⁻¹ = a ^ j := by
    rw [← hj]
    group
  rw [← conj_pow, hy, inv_pow] at h1
  have h2 : a ^ (j + j) = 1 := by
    rw [pow_add]
    calc a ^ j * a ^ j = (a ^ j)⁻¹ * a ^ j := by rw [h1]
      _ = 1 := inv_mul_cancel _
  have h3 : 2 ^ (n - 1) ∣ j + j := by
    rw [← ha]
    exact orderOf_dvd_of_pow_eq_one h2
  have h4 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have h5 : 2 ^ (n - 2) ∣ j := by
    rw [h4, show j + j = 2 * j by ring] at h3
    exact Nat.dvd_of_mul_dvd_mul_left two_pos h3
  rw [hj]
  exact pow_eq_one_or_of_dvd hn ha h5

theorem sq_cases_sd {n : ℕ} (hn : 4 ≤ n) {a y : P} (ha : orderOf a = 2 ^ (n - 1))
    (hM : (zpowers a).index = 2) (hy : y * a * y⁻¹ = a ^ (2 ^ (n - 2) - 1)) :
    y * y = 1 ∨ y * y = a ^ (2 ^ (n - 2)) := by
  obtain ⟨j, hj⟩ := exists_sq_pow y hM
  have h1 : y * a ^ j * y⁻¹ = a ^ j := by
    rw [← hj]
    group
  rw [← conj_pow, hy, ← pow_mul] at h1
  have hge : 1 ≤ 2 ^ (n - 2) - 1 := by
    have : 4 ≤ 2 ^ (n - 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right two_pos (by omega)
    omega
  have h2 : a ^ ((2 ^ (n - 2) - 1 - 1) * j) = 1 := by
    have e : (2 ^ (n - 2) - 1) * j = (2 ^ (n - 2) - 1 - 1) * j + j := by
      rw [← add_one_mul]
      congr 1
      omega
    rw [e, pow_add] at h1
    exact mul_eq_right.mp h1
  have h3 : 2 ^ (n - 1) ∣ (2 ^ (n - 2) - 2) * j := by
    rw [← ha, show 2 ^ (n - 2) - 2 = 2 ^ (n - 2) - 1 - 1 by omega]
    exact orderOf_dvd_of_pow_eq_one h2
  rw [hj]
  exact pow_eq_one_or_of_dvd hn ha (dvd_of_dvd_mul_pred hn h3)

theorem exists_shape_of_maxClass {n : ℕ} (hn : 4 ≤ n) (hP : Nat.card P = 2 ^ n)
    (hcl : n - 1 ≤ Group.nilpotencyClass P) :
    ∃ a y : P, orderOf a = 2 ^ (n - 1) ∧ y ∉ zpowers a ∧
      Subgroup.closure ({a, y} : Set P) = ⊤ ∧
      ((y * y = 1 ∧ y * a * y⁻¹ = a⁻¹) ∨ (y * y = a ^ (2 ^ (n - 2)) ∧ y * a * y⁻¹ = a⁻¹) ∨
        (y * y = 1 ∧ y * a * y⁻¹ = a ^ (2 ^ (n - 2) - 1))) := by
  obtain ⟨M, hMidx, hMcyc⟩ := exists_cyclic_index_two n (by omega) P hP hcl
  have hZ : Nat.card (center P) = 2 := card_center_of_maxClass Nat.prime_two hn hP hcl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
  set a : P := (g : P) with ha_def
  have hzM : zpowers a = M := by
    refine le_antisymm (Subgroup.zpowers_le.mpr g.2) (fun m hm => ?_)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨m, hm⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hMidx' : (zpowers a).index = 2 := hzM ▸ hMidx
  have hMcard : Nat.card M = 2 ^ (n - 1) := by
    have h1 := Subgroup.card_mul_index M
    rw [hMidx, hP] at h1
    have : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this] at h1
    exact Nat.eq_of_mul_eq_mul_right two_pos h1
  have ha : orderOf a = 2 ^ (n - 1) := by
    rw [← hMcard, ha_def, Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have ha1 : a ^ (2 ^ (n - 1)) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  obtain ⟨y, hyM⟩ : ∃ y : P, y ∉ M := by
    by_contra hcon
    have : M = ⊤ := eq_top_iff.mpr (fun x _ => by_contra (fun hx => hcon ⟨x, hx⟩))
    rw [← Subgroup.index_eq_one] at this
    omega
  have hy : y ∉ zpowers a := hzM ▸ hyM
  have hcl' := closure_pair_eq_top hMidx' hy
  rcases conj_exponent_cases hn ha hMidx' y with h1 | h2 | h3 | h4
  · exact (false_of_exponent_one hn ha hcl' hZ (Or.inl h1)).elim
  · exact (false_of_exponent_one hn ha hcl' hZ (Or.inr h2)).elim
  · rcases sq_cases_sd hn ha hMidx' h3 with hy2 | hy2
    · exact ⟨a, y, ha, hy, hcl', Or.inr (Or.inr ⟨hy2, h3⟩)⟩
    · have hy' : y * a ∉ zpowers a := by
        intro h
        apply hy
        have := (zpowers a).mul_mem h ((zpowers a).inv_mem (Subgroup.mem_zpowers a))
        simpa using this
      have hq : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
      have h2n : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      have hsq : y * a * (y * a) = 1 := by
        have e : y * a * (y * a) = (y * a * y⁻¹) * (y * y) * a := by group
        rw [e, h3, hy2, ← pow_add, ← pow_succ]
        have : 2 ^ (n - 2) - 1 + 2 ^ (n - 2) + 1 = 2 ^ (n - 1) := by omega
        rw [this, ha1]
      have hconj : y * a * a * (y * a)⁻¹ = a ^ (2 ^ (n - 2) - 1) := by
        rw [← h3]
        group
      exact ⟨a, y * a, ha, hy', closure_pair_eq_top hMidx' hy',
        Or.inr (Or.inr ⟨hsq, hconj⟩)⟩
  · rcases sq_cases_inv hn ha hMidx' h4 with hy2 | hy2
    · exact ⟨a, y, ha, hy, hcl', Or.inl ⟨hy2, h4⟩⟩
    · exact ⟨a, y, ha, hy, hcl', Or.inr (Or.inl ⟨hy2, h4⟩)⟩

end Shape

end CFSG.GH74.Uniqueness.SU.SU1
