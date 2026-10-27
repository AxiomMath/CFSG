module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11c_dih_conj {t t' : G} (ht : t * t = 1) (ht' : t' * t' = 1) (k : ℤ) :
    t * (t * t') ^ k * t⁻¹ = (t * t') ^ (-k) := by
  have hconj : t * (t * t') * t⁻¹ = (t * t')⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, inv_eq_of_mul_eq_one_right ht',
      ← mul_assoc, ht, one_mul]
  rw [← conj_zpow (a := t) (b := t * t') (i := k), hconj, inv_zpow']

private theorem sec11c_dih_conj' {t t' : G} (ht : t * t = 1) (ht' : t' * t' = 1) (k : ℤ) :
    t * (t * t') ^ k * t = (t * t') ^ (-k) := by
  have h := sec11c_dih_conj ht ht' k
  rwa [inv_eq_of_mul_eq_one_right ht] at h

private theorem sec11c_dih_conj_rho {t t' ρ : G} (ht : t * t = 1) (ht' : t' * t' = 1)
    (hρ : ρ = t * t') (k : ℤ) : t * ρ ^ k * t = ρ ^ (-k) := by
  rw [hρ]
  exact sec11c_dih_conj' ht ht' k

private theorem sec11c_zpow_mul_t {t t' : G} (ht : t * t = 1) (ht' : t' * t' = 1) (i : ℤ) :
    (t * t') ^ i * t = t * (t * t') ^ (-i) := by
  have h1 : t * (t * (t * t') ^ i * t) = (t * t') ^ i * t := by
    rw [← mul_assoc t (t * (t * t') ^ i) t, ← mul_assoc t t ((t * t') ^ i), ht, one_mul]
  rw [← h1, sec11c_dih_conj' ht ht' i]

private theorem sec11_zpow_mul_t_rho {t t' ρ : G} (ht : t * t = 1) (ht' : t' * t' = 1)
    (hρ : ρ = t * t') (i : ℤ) : ρ ^ i * t = t * ρ ^ (-i) := by
  rw [hρ]
  exact sec11c_zpow_mul_t ht ht' i

private theorem sec11c_dih_sq_rho {t t' ρ : G} (ht : t * t = 1) (ht' : t' * t' = 1)
    (hρ : ρ = t * t') (k : ℤ) : t * ρ ^ k * (t * ρ ^ k) = 1 := by
  calc t * ρ ^ k * (t * ρ ^ k)
      = (t * ρ ^ k * t) * ρ ^ k := by rw [← mul_assoc]
    _ = ρ ^ (-k) * ρ ^ k := by rw [sec11c_dih_conj_rho ht ht' hρ k]
    _ = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]

theorem sec11c_dih_sq {t t' : G} (ht : t * t = 1) (ht' : t' * t' = 1) (k : ℤ) :
    t * (t * t') ^ k * (t * (t * t') ^ k) = 1 := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  calc t * (t * t') ^ k * (t * (t * t') ^ k)
      = (t * (t * t') ^ k * t) * (t * t') ^ k := by rw [← mul_assoc]
    _ = (t * (t * t') ^ k * t⁻¹) * (t * t') ^ k := by rw [htinv]
    _ = (t * t') ^ (-k) * (t * t') ^ k := by rw [sec11c_dih_conj ht ht' k]
    _ = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]

theorem sec11c_dih_mem {t t' d : G} (ht : t * t = 1) (ht' : t' * t' = 1)
    (hd : d ∈ zpowers t ⊔ zpowers t') : ∃ k : ℤ, d = (t * t') ^ k ∨ d = t * (t * t') ^ k := by
  have hcl : zpowers t ⊔ zpowers t' = Subgroup.closure ({t, t'} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    rfl
  rw [hcl] at hd
  refine Subgroup.closure_induction
    (p := fun d _ => ∃ k : ℤ, d = (t * t') ^ k ∨ d = t * (t * t') ^ k) ?_ ?_ ?_ ?_ hd
  · intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by rw [zpow_zero, mul_one])⟩
    · exact ⟨1, Or.inr (by rw [zpow_one, ← mul_assoc, ht, one_mul])⟩
  · exact ⟨0, Or.inl (by rw [zpow_zero])⟩
  · intro x y _ _ hx hy
    rcases hx with ⟨a, ha | ha⟩ <;> rcases hy with ⟨b, hb | hb⟩
    · exact ⟨a + b, Or.inl (by rw [ha, hb, ← zpow_add])⟩
    · refine ⟨b - a, Or.inr ?_⟩
      rw [ha, hb, ← mul_assoc, sec11c_zpow_mul_t ht ht' a, mul_assoc, ← zpow_add,
        show -a + b = b - a by ring]
    · refine ⟨a + b, Or.inr ?_⟩
      rw [ha, hb, mul_assoc, ← zpow_add]
    · refine ⟨b - a, Or.inl ?_⟩
      rw [ha, hb, ← mul_assoc, sec11c_dih_conj' ht ht' a, ← zpow_add,
        show -a + b = b - a by ring]
  · intro x _ hx
    obtain ⟨a, ha | ha⟩ := hx
    · exact ⟨-a, Or.inl (by rw [ha, zpow_neg])⟩
    · exact ⟨a, Or.inr (by rw [ha, inv_eq_of_mul_eq_one_right (sec11c_dih_sq ht ht' a)])⟩

structure Sec11cDih (G : Type) [Group G] (D : Subgroup G) (t t' z : G) : Prop where
  t_sq : t * t = 1
  t'_sq : t' * t' = 1
  eq : D = zpowers t ⊔ zpowers t'
  two : IsPGroup 2 D
  nonab : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a
  z_mem : z ∈ D
  z_cent : ∀ d ∈ D, d * z = z * d
  z_sq : z * z = 1
  z_ne : z ≠ 1
  t_ne : t ≠ z

namespace Sec11cDih

variable {D : Subgroup G} {t t' z : G}

private theorem sec11_even_of_four_dvd {n : ℕ} (h4 : 4 ∣ n) {j : ℤ} (hj : (n : ℤ) ∣ j) :
    Even j := by
  obtain ⟨c, rfl⟩ := h4
  obtain ⟨k, hk⟩ := hj
  rw [even_iff_two_dvd]
  exact ⟨2 * (c : ℤ) * k, by rw [hk]; push_cast; ring⟩

private theorem sec11_even_of_four_dvd_two_mul {n : ℕ} (h4 : 4 ∣ n) {j : ℤ}
    (hj : (n : ℤ) ∣ 2 * j) : Even j := by
  obtain ⟨c, rfl⟩ := h4
  obtain ⟨k, hk⟩ := hj
  rw [even_iff_two_dvd]
  refine ⟨(c : ℤ) * k, ?_⟩
  have h2 : (2 : ℤ) * j = 2 * (2 * ((c : ℤ) * k)) := by rw [hk]; push_cast; ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

private theorem sec11_odd_of_orderOf_zpow_eq [Finite G] {ρ : G} (h4 : 4 ∣ orderOf ρ) {b : ℤ}
    (hord : orderOf (ρ ^ b) = orderOf ρ) : Odd b := by
  by_contra hb
  rw [Int.not_odd_iff_even] at hb
  obtain ⟨c, hc⟩ := hb
  rw [show b = 2 * c from by rw [hc]; ring] at hord
  have hpow : (ρ ^ (2 * c)) ^ (orderOf ρ / 2) = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    rw [show (2 : ℤ) * c * ((orderOf ρ / 2 : ℕ) : ℤ) = c * (orderOf ρ : ℤ) by
      have h2 : 2 ∣ orderOf ρ := dvd_trans (by norm_num : 2 ∣ 4) h4
      have hone : ((orderOf ρ / 2 : ℕ) : ℤ) * 2 = (orderOf ρ : ℤ) := by
        exact_mod_cast Nat.div_mul_cancel h2
      calc (2 : ℤ) * c * ((orderOf ρ / 2 : ℕ) : ℤ) = c * (((orderOf ρ / 2 : ℕ) : ℤ) * 2) := by
            ring
        _ = c * (orderOf ρ : ℤ) := by rw [hone]]
    rw [zpow_mul', zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hdvd : orderOf ρ ∣ orderOf ρ / 2 := by
    have := orderOf_dvd_of_pow_eq_one hpow
    rwa [hord] at this
  have h4le : 4 ≤ orderOf ρ := Nat.le_of_dvd (orderOf_pos ρ) h4
  have hle : orderOf ρ ≤ orderOf ρ / 2 := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem sec11c_conj_mul_zpow {G : Type} [Group G] (y t ρ : G) (k : ℤ) :
    y * (t * ρ ^ k) * y⁻¹ = (y * t * y⁻¹) * (y * ρ * y⁻¹) ^ k := by
  rw [conj_zpow (a := y) (b := ρ) (i := k)]
  group

private theorem sec11c_conj_t_rho {t t' ρ : G} (ht : t * t = 1) (ht' : t' * t' = 1)
    (hρ : ρ = t * t') (i : ℤ) : (t * ρ ^ i) * t * (t * ρ ^ i)⁻¹ = t * ρ ^ (2 * i) := by
  rw [inv_eq_of_mul_eq_one_right (sec11c_dih_sq_rho ht ht' hρ i)]
  calc (t * ρ ^ i) * t * (t * ρ ^ i)
      = ((t * ρ ^ i) * t) * (t * ρ ^ i) := rfl
    _ = ρ ^ (-i) * (t * ρ ^ i) := by rw [sec11c_dih_conj_rho ht ht' hρ i]
    _ = (ρ ^ (-i) * t) * ρ ^ i := by rw [← mul_assoc]
    _ = (t * ρ ^ i) * ρ ^ i := by rw [sec11_zpow_mul_t_rho ht ht' hρ (-i), neg_neg]
    _ = t * ρ ^ (2 * i) := by rw [mul_assoc, ← zpow_add, show i + i = 2 * i by ring]

private theorem sec11c_rho_ne_comm (h : Sec11cDih G D t t' z) : t * t' ≠ t' * t := by
  intro hcomm
  have htρ : Commute t (t * t') := by
    show t * (t * t') = (t * t') * t
    rw [show t * (t * t') = t' by rw [← mul_assoc, h.t_sq, one_mul],
      show (t * t') * t = t' by rw [mul_assoc, ← hcomm, ← mul_assoc, h.t_sq, one_mul]]
  have ht'ρ : Commute t' (t * t') := by
    show t' * (t * t') = (t * t') * t'
    rw [show t' * (t * t') = t by rw [← mul_assoc, ← hcomm, mul_assoc, h.t'_sq, mul_one],
      show (t * t') * t' = t by rw [mul_assoc, h.t'_sq, mul_one]]
  obtain ⟨a, ha, b, hb, hab⟩ := h.nonab
  rw [h.eq] at ha hb
  rcases sec11c_dih_mem h.t_sq h.t'_sq ha with ⟨m, hm | hm⟩
  all_goals rcases sec11c_dih_mem h.t_sq h.t'_sq hb with ⟨n, hn | hn⟩
  · rw [hm, hn] at hab
    exact hab ((Commute.refl (t * t')).zpow_zpow m n).eq
  · rw [hm, hn] at hab
    exact hab ((htρ.symm.zpow_left m).mul_right
      ((Commute.refl (t * t')).zpow_zpow m n)).eq
  · rw [hm, hn] at hab
    exact hab ((htρ.zpow_right n).mul_left
      ((Commute.refl (t * t')).zpow_zpow m n)).eq
  · rw [hm, hn] at hab
    exact hab (((Commute.refl t).mul_right (htρ.zpow_right n)).mul_left
      ((htρ.symm.zpow_left m).mul_right ((Commute.refl (t * t')).zpow_zpow m n))).eq

private theorem sec11c_rho_sq_ne_one (h : Sec11cDih G D t t' z) : (t * t') ^ 2 ≠ 1 := by
  intro h2
  apply sec11c_rho_ne_comm h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right h.t'_sq
  have hρ2 : (t * t') * (t * t') = 1 := by rw [← pow_two, h2]
  have h1 : (t * t')⁻¹ = t * t' := inv_eq_of_mul_eq_one_right hρ2
  rw [mul_inv_rev, ht'inv, htinv] at h1
  exact h1.symm

private theorem sec11c_t_ne_one (h : Sec11cDih G D t t' z) : t ≠ 1 := by
  intro h1
  exact sec11c_rho_ne_comm h (by rw [h1, one_mul, mul_one])

private theorem sec11c_t'_ne_one (h : Sec11cDih G D t t' z) : t' ≠ 1 := by
  intro h1
  exact sec11c_rho_ne_comm h (by rw [h1, mul_one, one_mul])

private theorem sec11c_t'_ne_z (h : Sec11cDih G D t t' z) : t' ≠ z := by
  intro hz
  have htD : t ∈ D := by rw [h.eq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  exact sec11c_rho_ne_comm h (by rw [hz, h.z_cent t htD])

theorem z_mem_zpowers [Finite G] (h : Sec11cDih G D t t' z) : z ∈ zpowers (t * t') := by
  set ρ := t * t' with hρ
  by_contra hz
  have htD : t ∈ D := by rw [h.eq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have ht'D : t' ∈ D := by rw [h.eq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t')
  have hρD : ρ ∈ D := by
    rw [hρ, h.eq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) (Subgroup.mem_zpowers t')
  have hzD : z ∈ zpowers t ⊔ zpowers t' := by rw [← h.eq]; exact h.z_mem
  obtain ⟨k, hk | hk⟩ := sec11c_dih_mem h.t_sq h.t'_sq hzD
  · rw [← hρ] at hk
    exact hz (hk.symm ▸ Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  · rw [← hρ] at hk
    exfalso
    have hzt : z * t = t * z := (h.z_cent t htD).symm
    have hL : z * t = ρ ^ (-k) := by rw [hk, sec11c_dih_conj_rho h.t_sq h.t'_sq hρ k]
    have hR : t * z = ρ ^ k := by rw [hk, ← mul_assoc, h.t_sq, one_mul]
    have heq : ρ ^ (-k) = ρ ^ k := by rw [← hL, ← hR, hzt]
    have e1 : ρ ^ ((2 : ℤ) * k) = 1 := by
      calc ρ ^ ((2 : ℤ) * k) = ρ ^ k * ρ ^ k := by
            rw [show (2 : ℤ) * k = k + k by ring, zpow_add]
        _ = ρ ^ k * ρ ^ (-k) := by rw [heq]
        _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
    have ht_z : t = z * ρ ^ k := by
      calc t = t * ρ ^ ((2 : ℤ) * k) := by rw [e1, mul_one]
        _ = t * (ρ ^ k * ρ ^ k) := by
              rw [show (2 : ℤ) * k = k + k by ring, zpow_add]
        _ = (t * ρ ^ k) * ρ ^ k := by rw [mul_assoc]
        _ = z * ρ ^ k := by rw [← hk]
    have ht'_z : t' = z * ρ ^ (k + 1) := by
      calc t' = t * ρ := by rw [hρ, ← mul_assoc, h.t_sq, one_mul]
        _ = (z * ρ ^ k) * ρ := by rw [ht_z]
        _ = z * ρ ^ (k + 1) := by rw [mul_assoc, ← zpow_add_one]
    have hzA : Commute z (ρ ^ (k + 1)) :=
      (h.z_cent (ρ ^ (k + 1)) (Subgroup.zpow_mem D hρD (k + 1))).symm
    have hsq2 : (z * ρ ^ (k + 1)) * (z * ρ ^ (k + 1)) = ρ ^ (2 * (k + 1)) := by
      have hcomm : (z * ρ ^ (k + 1)) * (z * ρ ^ (k + 1))
          = z * z * (ρ ^ (k + 1) * ρ ^ (k + 1)) :=
        (hzA.symm).mul_mul_mul_comm z (ρ ^ (k + 1))
      rw [hcomm, h.z_sq, one_mul, ← zpow_add,
        show (k + 1) + (k + 1) = 2 * (k + 1) by ring]
    have hsq : (z * ρ ^ (k + 1)) * (z * ρ ^ (k + 1)) = 1 := by rw [← ht'_z, h.t'_sq]
    have e2 : ρ ^ ((2 : ℤ) * k + 2) = 1 := by
      rw [show (2 : ℤ) * (k + 1) = (2 : ℤ) * k + 2 by ring] at hsq2
      rw [← hsq2, hsq]
    have hsq_rho : ρ * ρ = 1 := by
      have h := zpow_add ρ ((2 : ℤ) * k) 2
      rw [e1, e2] at h
      have h2 : ρ ^ (2 : ℤ) = 1 := by simpa using h.symm
      rwa [zpow_two] at h2
    have ht't : t * t' = t' * t := by
      have h1 : (t * t')⁻¹ = t * t' := by
        rw [hρ] at hsq_rho
        exact inv_eq_of_mul_eq_one_right hsq_rho
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.t_sq, inv_eq_of_mul_eq_one_right h.t'_sq] at h1
      exact h1.symm
    exact sec11c_rho_ne_comm h ht't

private theorem sec11c_eq_of_orderOf_eq_two_of_isCyclic {G : Type*} [Group G] {K : Subgroup G}
    [Finite K] (hK : IsCyclic K) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) : x = y := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h2 : 2 ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← hx2]
    exact Subgroup.orderOf_dvd_natCard K hx
  have h := IsCyclic.card_orderOf_eq_totient (α := K) h2
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : (⟨x, hx⟩ : K) ∈ ({a} : Finset K) :=
    ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Subgroup.orderOf_mk]⟩
  have hya : (⟨y, hy⟩ : K) ∈ ({a} : Finset K) :=
    ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Subgroup.orderOf_mk]⟩
  rw [Finset.mem_singleton] at hxa hya
  exact congrArg Subtype.val (hxa.trans hya.symm)

private theorem sec11c_eq_z_of_mem_zpowers_of_sq [Finite G] {D : Subgroup G} {t t' z : G}
    (h : Sec11cDih G D t t' z) {x : G} (hx : x ∈ zpowers (t * t')) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : x = z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact sec11c_eq_of_orderOf_eq_two_of_isCyclic (Subgroup.isCyclic_zpowers (t * t')) hx
    (z_mem_zpowers h) (orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1)
    (orderOf_eq_prime (by rw [pow_two]; exact h.z_sq) h.z_ne)

theorem four_dvd [Finite G] (h : Sec11cDih G D t t' z) : 4 ∣ orderOf (t * t') := by
  have hρD : t * t' ∈ D := by
    rw [h.eq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) (Subgroup.mem_zpowers t')
  obtain ⟨n, hn⟩ := h.two ⟨t * t', hρD⟩
  have horder : orderOf ((⟨t * t', hρD⟩ : D)) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  rw [Subgroup.orderOf_mk] at horder
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp horder
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm01 : m = 0 ∨ m = 1 := by omega
    have hdvd : orderOf (t * t') ∣ 2 := by
      rcases hm01 with rfl | rfl
      · rw [hm]; norm_num
      · rw [hm]; norm_num
    exact sec11c_rho_sq_ne_one h ((orderOf_dvd_iff_pow_eq_one).mp hdvd)
  rw [hm]
  have h : 2 ^ 2 ∣ 2 ^ m := pow_dvd_pow 2 hm2
  rwa [show (2 : ℕ) ^ 2 = 4 by norm_num] at h

theorem even_of_zpow_mem [Finite G] (h : Sec11cDih G D t t' z) {j : ℤ}
    (hj : (t * t') ^ j ∈ zpowers z) : Even j := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hj
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, h.z_sq]
  rcases Int.even_or_odd' m with ⟨s, hs | hs⟩
  · have hzm : z ^ m = 1 := by rw [hs, zpow_mul, hz2, one_zpow]
    have hρj : (t * t') ^ j = 1 := by rw [← hm, hzm]
    exact sec11_even_of_four_dvd (four_dvd h) ((orderOf_dvd_iff_zpow_eq_one).mpr hρj)
  · have hzm : z ^ m = z := by
      rw [hs, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]
    have hρj : (t * t') ^ j = z := by rw [← hm, hzm]
    have h2j : (t * t') ^ (2 * j) = 1 := by
      rw [show 2 * j = j * 2 by ring, zpow_mul, hρj, zpow_two, h.z_sq]
    exact sec11_even_of_four_dvd_two_mul (four_dvd h)
      ((orderOf_dvd_iff_zpow_eq_one).mpr h2j)

theorem mem_class_iff [Finite G] (h : Sec11cDih G D t t' z) (k : ℤ) :
    t * (t * t') ^ k ∈ conjClassIn D t ↔ Even k := by
  have h4 : 4 ∣ orderOf (t * t') := four_dvd h
  constructor
  · intro hmem
    obtain ⟨d, hdD, hd⟩ := hmem
    have hd' : d ∈ zpowers t ⊔ zpowers t' := by rw [← h.eq]; exact hdD
    obtain ⟨i, hi | hi⟩ := sec11c_dih_mem h.t_sq h.t'_sq hd'
    · rw [hi] at hd
      have hR : (t * t') ^ i * t * ((t * t') ^ i)⁻¹ = t * (t * t') ^ (-(2 * i)) := by
        rw [show ((t * t') ^ i)⁻¹ = (t * t') ^ (-i) by rw [zpow_neg],
          sec11c_zpow_mul_t h.t_sq h.t'_sq i, mul_assoc, ← zpow_add,
          show -i + -i = -(2 * i) by ring]
      have heq : (t * t') ^ k = (t * t') ^ (-(2 * i)) := by
        rw [hR] at hd
        exact mul_left_cancel hd
      have hthis : (t * t') ^ (k + 2 * i) = 1 := by
        rw [zpow_add, heq, ← zpow_add, show -(2 * i) + 2 * i = 0 by ring, zpow_zero]
      have heven : Even (k + 2 * i) :=
        sec11_even_of_four_dvd h4 ((orderOf_dvd_iff_zpow_eq_one).mpr hthis)
      exact (Int.even_add.mp heven).mpr ⟨i, by ring⟩
    · rw [hi] at hd
      have hR : (t * (t * t') ^ i) * t * (t * (t * t') ^ i)⁻¹ = t * (t * t') ^ (2 * i) :=
        sec11c_conj_t_rho h.t_sq h.t'_sq rfl i
      have heq : (t * t') ^ k = (t * t') ^ (2 * i) := by
        rw [hR] at hd
        exact mul_left_cancel hd
      have hthis : (t * t') ^ (k - 2 * i) = 1 := by
        rw [sub_eq_add_neg, zpow_add, heq, ← zpow_add, show 2 * i + -(2 * i) = 0 by ring,
          zpow_zero]
      have heven : Even (k - 2 * i) :=
        sec11_even_of_four_dvd h4 ((orderOf_dvd_iff_zpow_eq_one).mpr hthis)
      exact (Int.even_sub.mp heven).mpr ⟨i, by ring⟩
  · intro hk
    obtain ⟨i, hi⟩ := hk
    rw [show k = 2 * i from by rw [hi]; ring]
    refine ⟨(t * t') ^ (-i), ?_, ?_⟩
    · have hmem : t * t' ∈ D := by
        rw [h.eq]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) (Subgroup.mem_zpowers t')
      exact Subgroup.zpow_mem D hmem (-i)
    · rw [show ((t * t') ^ (-i))⁻¹ = (t * t') ^ i by rw [zpow_neg, inv_inv]]
      rw [sec11c_zpow_mul_t h.t_sq h.t'_sq (-i), neg_neg, mul_assoc, ← zpow_add,
        show i + i = 2 * i by ring]

theorem conj_form [Finite G] (h : Sec11cDih G D t t' z) {y : G}
    (hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D) (hyz : y * z = z * y) :
    ∃ a b : ℤ, y * t * y⁻¹ = t * (t * t') ^ a ∧ y * (t * t') * y⁻¹ = (t * t') ^ b ∧ Odd b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := t * t' with hρ
  have htD : t ∈ D := by rw [h.eq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have ht'D : t' ∈ D := by rw [h.eq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t')
  have hytmem : y * t * y⁻¹ ∈ zpowers t ⊔ zpowers t' := by rw [← h.eq]; exact hyD t htD
  have hyt'mem : y * t' * y⁻¹ ∈ zpowers t ⊔ zpowers t' := by rw [← h.eq]; exact hyD t' ht'D
  have ha : ∃ a : ℤ, y * t * y⁻¹ = t * ρ ^ a := by
    obtain ⟨c, hc | hc⟩ := sec11c_dih_mem h.t_sq h.t'_sq hytmem
    · exfalso
      have hsq : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
        have h2 : y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
        rw [h2, h.t_sq, mul_one, mul_inv_cancel]
      have hne : y * t * y⁻¹ ≠ 1 := by
        intro h1
        apply sec11c_t_ne_one h
        calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
          _ = 1 := by rw [h1]; group
      have hz_eq : y * t * y⁻¹ = z := by
        refine sec11c_eq_z_of_mem_zpowers_of_sq h ?_ hsq hne
        exact hc.symm ▸ Subgroup.mem_zpowers_iff.mpr ⟨c, rfl⟩
      exact h.t_ne (by
        calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
          _ = z := by rw [hz_eq]; exact ((commute_iff_eq y z).mpr hyz).inv_mul_cancel)
    · exact ⟨c, by rw [hρ]; exact hc⟩
  have ha' : ∃ a' : ℤ, y * t' * y⁻¹ = t * ρ ^ a' := by
    obtain ⟨c, hc | hc⟩ := sec11c_dih_mem h.t_sq h.t'_sq hyt'mem
    · exfalso
      have hsq : (y * t' * y⁻¹) * (y * t' * y⁻¹) = 1 := by
        have h2 : y * t' * y⁻¹ * (y * t' * y⁻¹) = y * (t' * t') * y⁻¹ := by group
        rw [h2, h.t'_sq, mul_one, mul_inv_cancel]
      have hne : y * t' * y⁻¹ ≠ 1 := by
        intro h1
        apply sec11c_t'_ne_one h
        calc t' = y⁻¹ * (y * t' * y⁻¹) * y := by group
          _ = 1 := by rw [h1]; group
      have hz_eq : y * t' * y⁻¹ = z := by
        refine sec11c_eq_z_of_mem_zpowers_of_sq h ?_ hsq hne
        exact hc.symm ▸ Subgroup.mem_zpowers_iff.mpr ⟨c, rfl⟩
      exact sec11c_t'_ne_z h (by
        calc t' = y⁻¹ * (y * t' * y⁻¹) * y := by group
          _ = z := by rw [hz_eq]; exact ((commute_iff_eq y z).mpr hyz).inv_mul_cancel)
    · exact ⟨c, by rw [hρ]; exact hc⟩
  obtain ⟨a, ha⟩ := ha
  obtain ⟨a', ha'⟩ := ha'
  have hρconj : y * ρ * y⁻¹ = ρ ^ (a' - a) := by
    rw [show y * ρ * y⁻¹ = (y * t * y⁻¹) * (y * t' * y⁻¹) by rw [hρ]; group, ha, ha']
    rw [show (t * ρ ^ a) * (t * ρ ^ a') = (t * ρ ^ a * t) * ρ ^ a' by rw [← mul_assoc]]
    rw [sec11c_dih_conj_rho h.t_sq h.t'_sq hρ a]
    rw [← zpow_add]
    congr 1
    ring
  have horder : orderOf (y * ρ * y⁻¹) = orderOf ρ := by
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective ρ
  have hpow : orderOf (ρ ^ (a' - a)) = orderOf ρ := by rw [← hρconj]; exact horder
  exact ⟨a, a' - a, ha, hρconj,
    sec11_odd_of_orderOf_zpow_eq (by rw [hρ]; exact four_dvd h) hpow⟩

theorem comm_not_mem [Finite G] (h : Sec11cDih G D t t' z) {y : G}
    (hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D) (hyz : y * z = z * y) (hy : y * t * y⁻¹ ∉ conjClassIn D t)
    {u : G} (hu : u ∈ D) (hur : u ∉ zpowers (t * t')) : y * u * y⁻¹ * u⁻¹ ∉ zpowers z := by
  obtain ⟨a, b, ha, hb, hbodd⟩ := conj_form h hyD hyz
  have haodd : Odd a := by
    rw [ha] at hy
    exact Int.not_even_iff_odd.mp (fun he => hy ((mem_class_iff h a).mpr he))
  have huD : u ∈ zpowers t ⊔ zpowers t' := by rw [← h.eq]; exact hu
  obtain ⟨k, hk | hk⟩ := sec11c_dih_mem h.t_sq h.t'_sq huD
  · exact absurd (hk.symm ▸ Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩) hur
  · rw [hk]
    intro hmem
    have hconj : y * (t * (t * t') ^ k) * y⁻¹ = t * (t * t') ^ (a + b * k) := by
      rw [sec11c_conj_mul_zpow y t (t * t') k, ha, hb, ← zpow_mul, mul_assoc, ← zpow_add]
    have hcomm : y * (t * (t * t') ^ k) * y⁻¹ * (t * (t * t') ^ k)⁻¹
        = (t * t') ^ (-(a + (b - 1) * k)) := by
      rw [hconj, show (t * (t * t') ^ k)⁻¹ = (t * t') ^ (-k) * t by
        rw [mul_inv_rev, ← zpow_neg, inv_eq_of_mul_eq_one_right h.t_sq]]
      rw [show (t * (t * t') ^ (a + b * k)) * ((t * t') ^ (-k) * t)
          = t * ((t * t') ^ (a + b * k) * (t * t') ^ (-k)) * t by group]
      rw [← zpow_add, sec11c_dih_conj' h.t_sq h.t'_sq (a + b * k + -k)]
      congr 1
      ring
    rw [hcomm] at hmem
    have heven : Even (-(a + (b - 1) * k)) := even_of_zpow_mem h hmem
    have hb1 : Even (b - 1) := by
      obtain ⟨m, hm⟩ := hbodd
      exact ⟨m, by omega⟩
    have hbk : Even ((b - 1) * k) := Int.even_mul.mpr (Or.inl hb1)
    have hodd : Odd (a + (b - 1) * k) := Int.odd_add.mpr (iff_of_true haodd hbk)
    exact (Int.not_even_iff_odd.mpr (odd_neg.mpr hodd)) heven

theorem class_of_two [Finite G] (h : Sec11cDih G D t t' z) {y1 y2 : G}
    (hy1D : ∀ d ∈ D, y1 * d * y1⁻¹ ∈ D) (hy1z : y1 * z = z * y1)
    (hgD : ∀ d ∈ D, (y1⁻¹ * y2) * d * (y1⁻¹ * y2)⁻¹ ∈ D)
    (hgz : (y1⁻¹ * y2) * z = z * (y1⁻¹ * y2))
    (h1 : y1 * t * y1⁻¹ ∉ conjClassIn D t) (h2 : y2 * t * y2⁻¹ ∉ conjClassIn D t) :
    (y1⁻¹ * y2) * t * (y1⁻¹ * y2)⁻¹ ∈ conjClassIn D t := by
  obtain ⟨a1, b1, ha1, hb1, hb1odd⟩ := conj_form h hy1D hy1z
  obtain ⟨ag, bg, hag, hbg, hbgodd⟩ := conj_form h hgD hgz
  have ha1odd : Odd a1 := by
    rw [ha1] at h1
    exact Int.not_even_iff_odd.mp (fun he => h1 ((mem_class_iff h a1).mpr he))
  have hy2_eq : y2 * t * y2⁻¹ = t * (t * t') ^ (a1 + b1 * ag) := by
    have hy2 : y2 = y1 * (y1⁻¹ * y2) := by group
    rw [hy2]
    rw [show (y1 * (y1⁻¹ * y2)) * t * (y1 * (y1⁻¹ * y2))⁻¹
        = y1 * ((y1⁻¹ * y2) * t * (y1⁻¹ * y2)⁻¹) * y1⁻¹ by group]
    rw [hag, sec11c_conj_mul_zpow y1 t (t * t') ag, ha1, hb1, ← zpow_mul, mul_assoc, ← zpow_add]
  have hsum_odd : Odd (a1 + b1 * ag) := by
    rw [hy2_eq] at h2
    exact Int.not_even_iff_odd.mp (fun he => h2 ((mem_class_iff h (a1 + b1 * ag)).mpr he))
  have hag_even : Even ag := by
    have hba : Even (b1 * ag) := (Int.odd_add.mp hsum_odd).mp ha1odd
    rcases Int.even_mul.mp hba with hb1e | hage
    · exact absurd hb1e (Int.not_even_iff_odd.mpr hb1odd)
    · exact hage
  rw [hag]
  exact (mem_class_iff h ag).mpr hag_even

end Sec11cDih

end CFSG.OddStandard.SmallF3.Omega
