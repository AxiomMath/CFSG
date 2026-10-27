module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

section SD

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_isSemidihedral {P : Subgroup G} (hP : IsSemidihedral P)
    (hP2 : IsPGroup 2 P) {z t : G} (hzP : z ∈ P) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ x ∈ P, z * x = x * z) (htP : t ∈ P) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ z) :
    ∃ g ∈ P, g * t * g⁻¹ = z * t := by
  obtain ⟨a, b, h8, hcard, hb2, hbna, hbab, hcl⟩ := hP
  subst hcl
  have haP : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hbP : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  obtain ⟨s, hs⟩ := hP2.exists_card_eq
  have hmdvd : orderOf a ∣ 2 ^ s := hs ▸ Subgroup.orderOf_dvd_natCard _ haP
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hmdvd
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have : j ≤ 2 := by omega
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨r, hr⟩ : ∃ r : ℕ, orderOf a = 8 * r :=
    ⟨2 ^ (j - 3), by rw [hj, show j = (j - 3) + 3 by omega, pow_add]; simp [mul_comm]⟩
  have hr0 : 0 < r := by
    have := orderOf_pos a
    omega
  have hone : ∀ k : ℤ, a ^ k = 1 ↔ ((8 * r : ℕ) : ℤ) ∣ k := fun k => by
    rw [← hr]
    exact (orderOf_dvd_iff_zpow_eq_one).symm
  have heq : ∀ k l : ℤ, ((8 * r : ℕ) : ℤ) ∣ k - l → a ^ k = a ^ l := fun k l h => by
    have h1 : a ^ (k - l) = 1 := (hone _).mpr h
    rw [zpow_sub, mul_inv_eq_one] at h1
    exact h1
  have hbaZ : b * a * b⁻¹ = a ^ ((4 * r : ℤ) - 1) := by
    rw [hbab]
    have e : orderOf a / 2 - 1 = 4 * r - 1 := by omega
    rw [e, ← zpow_natCast]
    congr 1
    omega
  have hba : ∀ k : ℤ, b * a ^ k * b⁻¹ = a ^ (k * ((4 * r : ℤ) - 1)) := fun k => by
    rw [← conj_zpow, hbaZ, ← zpow_mul, mul_comm]
  have key : ∀ x ∈ Subgroup.closure ({a, b} : Set G), ∃ i : ℤ, x = a ^ i ∨ x = a ^ i * b := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, Or.inl (zpow_one _).symm⟩
      · exact ⟨0, Or.inr (by simp)⟩
    | one => exact ⟨0, Or.inl (by simp)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, hi⟩ := hx
      obtain ⟨k, hk⟩ := hy
      rcases hi with rfl | rfl <;> rcases hk with rfl | rfl
      · exact ⟨i + k, Or.inl (by rw [zpow_add])⟩
      · exact ⟨i + k, Or.inr (by rw [zpow_add, mul_assoc])⟩
      · refine ⟨i + k * ((4 * r : ℤ) - 1), Or.inr ?_⟩
        calc a ^ i * b * a ^ k = a ^ i * (b * a ^ k * b⁻¹) * b := by group
          _ = a ^ (i + k * ((4 * r : ℤ) - 1)) * b := by rw [hba k, zpow_add]
      · refine ⟨i + k * ((4 * r : ℤ) - 1), Or.inl ?_⟩
        calc a ^ i * b * (a ^ k * b) = a ^ i * (b * a ^ k * b⁻¹) * (b * b) := by group
          _ = a ^ (i + k * ((4 * r : ℤ) - 1)) := by rw [hba k, hb2, zpow_add, mul_one]
    | inv x _ hx =>
      obtain ⟨i, hi⟩ := hx
      rcases hi with rfl | rfl
      · exact ⟨-i, Or.inl (by rw [zpow_neg])⟩
      · refine ⟨-i * ((4 * r : ℤ) - 1), Or.inr ?_⟩
        calc (a ^ i * b)⁻¹ = b * a ^ (-i) := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb2,
              zpow_neg]
          _ = (b * a ^ (-i) * b⁻¹) * b := by group
          _ = a ^ (-i * ((4 * r : ℤ) - 1)) * b := by rw [hba (-i)]
  have hinv : ∀ i : ℤ, a ^ i * a ^ i = 1 → a ^ i = 1 ∨ a ^ i = a ^ ((4 * r : ℤ)) := by
    intro i hi
    rw [← zpow_add, hone] at hi
    obtain ⟨u, hu⟩ := hi
    have h4 : (4 * r : ℤ) ∣ i := by
      have : ((8 * r : ℕ) : ℤ) = 8 * r := by push_cast; ring
      rw [this] at hu
      exact ⟨u, by linarith⟩
    obtain ⟨w, hw⟩ := h4
    rcases Int.even_or_odd w with ⟨v, hv⟩ | ⟨v, hv⟩
    · left
      rw [hone]
      exact ⟨v, by push_cast; subst hv; linarith⟩
    · right
      apply heq
      exact ⟨v, by push_cast; subst hv; linarith⟩
  have hzeq : z = a ^ ((4 * r : ℤ)) := by
    obtain ⟨i, hi | hi⟩ := key z hzP
    · rcases hinv i (by rw [← hi]; exact hz2) with h | h
      · exact absurd (hi.trans h) hz1
      · exact hi.trans h
    · exfalso
      have hc := hzc a haP
      have h2 : b * a = a * b := by
        have h1 : a ^ i * (b * a) = a ^ i * (a * b) := by
          calc a ^ i * (b * a) = z * a := by rw [hi]; group
            _ = a * z := hc
            _ = a ^ i * (a * b) := by
              rw [hi, ← mul_assoc, ← mul_assoc, ← zpow_one_add, add_comm, zpow_add_one]
        exact mul_left_cancel h1
      have h3 : b * a * b⁻¹ = a := by rw [h2]; group
      rw [hbaZ] at h3
      have h4 : a ^ ((4 * r : ℤ) - 1 - 1) = 1 := by
        rw [zpow_sub, h3, zpow_one, mul_inv_cancel]
      obtain ⟨w, hw⟩ := (hone _).mp h4
      have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr0
      push_cast at hw
      rcases le_or_gt w 0 with hw0 | hw0
      · nlinarith
      · nlinarith
  obtain ⟨i, hi⟩ : ∃ i : ℤ, t = a ^ i * b := by
    obtain ⟨i, hi | hi⟩ := key t htP
    · exfalso
      rcases hinv i (by rw [← hi]; exact ht2) with h | h
      · exact ht1 (hi.trans h)
      · exact htz (hi.trans (h.trans hzeq.symm))
    · exact ⟨i, hi⟩
  refine ⟨a ^ ((2 * r : ℤ)), Subgroup.zpow_mem _ haP _, ?_⟩
  rw [hi, hzeq]
  calc a ^ ((2 * r : ℤ)) * (a ^ i * b) * (a ^ ((2 * r : ℤ)))⁻¹
      = a ^ ((2 * r : ℤ)) * a ^ i * (b * a ^ (-((2 * r : ℤ))) * b⁻¹) * b := by group
    _ = a ^ ((2 * r : ℤ) + i + (-((2 * r : ℤ))) * ((4 * r : ℤ) - 1)) * b := by
        rw [hba, ← zpow_add, ← zpow_add]
    _ = a ^ ((4 * r : ℤ)) * (a ^ i * b) := by
        rw [← mul_assoc, ← zpow_add]
        have h5 : a ^ ((2 * r : ℤ) + i + (-((2 * r : ℤ))) * ((4 * r : ℤ) - 1)) =
            a ^ ((4 * r : ℤ) + i) := heq _ _ ⟨-(r : ℤ), by push_cast; ring⟩
        rw [h5]

theorem exists_conj_of_isWreathed {P : Subgroup G} (hP : IsWreathed P) (hP2 : IsPGroup 2 P)
    {z t : G} (hzP : z ∈ P) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ x ∈ P, z * x = x * z)
    (htP : t ∈ P) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ z) :
    ∃ g ∈ P, g * t * g⁻¹ = z * t := by
  obtain ⟨a, c, b, h4, hca, hac, hcard, hb2, hbab, hbcb, hcl⟩ := hP
  subst hcl
  have haP : a ∈ Subgroup.closure ({a, c, b} : Set G) := Subgroup.subset_closure (by simp)
  have hcP : c ∈ Subgroup.closure ({a, c, b} : Set G) := Subgroup.subset_closure (by simp)
  have hbP : b ∈ Subgroup.closure ({a, c, b} : Set G) := Subgroup.subset_closure (by simp)
  obtain ⟨n, hn⟩ : ∃ n, orderOf a = n := ⟨_, rfl⟩
  rw [hn] at h4 hca hcard
  obtain ⟨s, hs⟩ := hP2.exists_card_eq
  have hndvd : n ∣ 2 ^ s := hn ▸ hs ▸ Subgroup.orderOf_dvd_natCard _ haP
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hndvd
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have : j ≤ 1 := by omega
    have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨h, hh⟩ : ∃ h : ℕ, n = 2 * h :=
    ⟨2 ^ (j - 1), by rw [hj, show j = (j - 1) + 1 by omega, pow_add]; simp [mul_comm]⟩
  have hh2 : 2 ≤ h := by omega
  have : NeZero n := ⟨by omega⟩
  have hna : ∀ k : ℤ, a ^ k = 1 ↔ (n : ℤ) ∣ k := fun k => by
    rw [← hn]; exact (orderOf_dvd_iff_zpow_eq_one).symm
  have hnc : ∀ k : ℤ, c ^ k = 1 ↔ (n : ℤ) ∣ k := fun k => by
    rw [← hca]; exact (orderOf_dvd_iff_zpow_eq_one).symm
  have hac' : Commute a c := hac
  have hcomm : ∀ k l : ℤ, c ^ l * a ^ k = a ^ k * c ^ l := fun k l =>
    ((hac'.zpow_zpow k l).eq).symm
  have hbA : ∀ k : ℤ, b * a ^ k * b⁻¹ = c ^ k := fun k => by
    rw [← conj_zpow, hbab]
  have hbC : ∀ k : ℤ, b * c ^ k * b⁻¹ = a ^ k := fun k => by
    rw [← conj_zpow, hbcb]
  have hmul : ∀ i j k l : ℤ, a ^ i * c ^ j * (a ^ k * c ^ l) = a ^ (i + k) * c ^ (j + l) :=
    fun i j k l => by
      calc a ^ i * c ^ j * (a ^ k * c ^ l) = a ^ i * (c ^ j * a ^ k) * c ^ l := by group
        _ = a ^ i * (a ^ k * c ^ j) * c ^ l := by rw [hcomm k j]
        _ = a ^ (i + k) * c ^ (j + l) := by rw [zpow_add, zpow_add]; group
  have key : ∀ x ∈ Subgroup.closure ({a, c, b} : Set G),
      ∃ i j : ℤ, x = a ^ i * c ^ j ∨ x = a ^ i * c ^ j * b := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, 0, Or.inl (by simp)⟩
      · exact ⟨0, 1, Or.inl (by simp)⟩
      · exact ⟨0, 0, Or.inr (by simp)⟩
    | one => exact ⟨0, 0, Or.inl (by simp)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, hi⟩ := hx
      obtain ⟨k, l, hk⟩ := hy
      rcases hi with rfl | rfl <;> rcases hk with rfl | rfl
      · exact ⟨i + k, j + l, Or.inl (hmul i j k l)⟩
      · exact ⟨i + k, j + l, Or.inr (by rw [← hmul i j k l]; group)⟩
      · refine ⟨i + l, j + k, Or.inr ?_⟩
        calc a ^ i * c ^ j * b * (a ^ k * c ^ l)
            = a ^ i * c ^ j * (b * a ^ k * b⁻¹) * (b * c ^ l * b⁻¹) * b := by group
          _ = a ^ i * c ^ j * (c ^ k * a ^ l) * b := by rw [hbA, hbC]; group
          _ = a ^ (i + l) * c ^ (j + k) * b := by
              rw [hcomm l k, hmul i j l k]
      · refine ⟨i + l, j + k, Or.inl ?_⟩
        calc a ^ i * c ^ j * b * (a ^ k * c ^ l * b)
            = a ^ i * c ^ j * (b * a ^ k * b⁻¹) * (b * c ^ l * b⁻¹) * (b * b) := by group
          _ = a ^ i * c ^ j * (c ^ k * a ^ l) * 1 := by rw [hbA, hbC, hb2]; group
          _ = a ^ (i + l) * c ^ (j + k) := by
              rw [hcomm l k, mul_one, hmul i j l k]
    | inv x _ hx =>
      obtain ⟨i, j, hi⟩ := hx
      rcases hi with rfl | rfl
      · exact ⟨-i, -j, Or.inl (by
          calc (a ^ i * c ^ j)⁻¹ = c ^ (-j) * a ^ (-i) := by rw [mul_inv_rev, zpow_neg, zpow_neg]
            _ = a ^ (-i) * c ^ (-j) := hcomm _ _)⟩
      · refine ⟨-j, -i, Or.inr ?_⟩
        calc (a ^ i * c ^ j * b)⁻¹ = b * (c ^ (-j) * a ^ (-i)) := by
              rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right hb2, zpow_neg, zpow_neg]
          _ = (b * c ^ (-j) * b⁻¹) * (b * a ^ (-i) * b⁻¹) * b := by group
          _ = a ^ (-j) * c ^ (-i) * b := by rw [hbC, hbA]
  have hnn : (n : ℤ) = 2 * h := by rw [hh]; push_cast; ring
  have hvala : ∀ k : ℤ, a ^ ((k : ZMod n).val) = a ^ k := fun k => by
    rw [← zpow_natCast, ZMod.val_intCast, ← hn, zpow_mod_orderOf]
  have hvalc : ∀ k : ℤ, c ^ ((k : ZMod n).val) = c ^ k := fun k => by
    rw [← zpow_natCast, ZMod.val_intCast, ← hca, zpow_mod_orderOf]
  have hdisj : ∀ i j : ℤ, a ^ i = c ^ j → a ^ i = 1 := by
    intro i j hij
    let f : ZMod n × ZMod n × ZMod 2 → ↥(Subgroup.closure ({a, c, b} : Set G)) := fun v =>
      ⟨a ^ v.1.val * c ^ v.2.1.val * b ^ v.2.2.val,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ haP _)
          (Subgroup.pow_mem _ hcP _)) (Subgroup.pow_mem _ hbP _)⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨i, j, hij | hij⟩ := key x hx
      · refine ⟨((i : ZMod n), (j : ZMod n), 0), Subtype.ext ?_⟩
        show a ^ ((i : ZMod n).val) * c ^ ((j : ZMod n).val) * b ^ (0 : ZMod 2).val = x
        rw [hvala, hvalc, ZMod.val_zero, pow_zero, mul_one, hij]
      · refine ⟨((i : ZMod n), (j : ZMod n), 1), Subtype.ext ?_⟩
        show a ^ ((i : ZMod n).val) * c ^ ((j : ZMod n).val) * b ^ (1 : ZMod 2).val = x
        have h1 : (1 : ZMod 2).val = 1 := rfl
        rw [hvala, hvalc, h1, pow_one, hij]
    have hcardle : Nat.card (ZMod n × ZMod n × ZMod 2) ≤
        Nat.card ↥(Subgroup.closure ({a, c, b} : Set G)) := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod, hcard]
      nlinarith
    have hinj := (hsurj.bijective_of_nat_card_le hcardle).1
    have h1 : f ((i : ZMod n), 0, 0) = f (0, (j : ZMod n), 0) := by
      apply Subtype.ext
      show a ^ ((i : ZMod n).val) * c ^ ((0 : ZMod n).val) * b ^ (0 : ZMod 2).val =
        a ^ ((0 : ZMod n).val) * c ^ ((j : ZMod n).val) * b ^ (0 : ZMod 2).val
      rw [hvala, hvalc]
      simp only [ZMod.val_zero, pow_zero, mul_one, one_mul]
      exact hij
    have h2 := hinj h1
    have h3 : ((i : ZMod n)) = 0 := congrArg Prod.fst h2
    exact (hna i).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd i n).mp h3)
  have hh0 : (h : ℤ) ≠ 0 := by
    have : (2 : ℤ) ≤ h := by exact_mod_cast hh2
    omega
  have hdiv2 : ∀ i : ℤ, (n : ℤ) ∣ 2 * i → ∃ u : ℤ, i = h * u := by
    intro i hi
    rw [hnn] at hi
    exact (mul_dvd_mul_iff_left (two_ne_zero)).mp hi
  have hpar : ∀ u : ℤ, (n : ℤ) ∣ h * u ↔ 2 ∣ u := by
    intro u
    rw [hnn, mul_comm 2 (h : ℤ)]
    exact mul_dvd_mul_iff_left hh0
  have hsq : ∀ i j : ℤ, a ^ i * c ^ j * (a ^ i * c ^ j) = 1 →
      (n : ℤ) ∣ 2 * i ∧ (n : ℤ) ∣ 2 * j := by
    intro i j hij
    rw [hmul] at hij
    have h1 : a ^ (i + i) = c ^ (-(j + j)) := by
      rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left hij
    have h2 : a ^ (i + i) = 1 := hdisj _ _ h1
    have h3 : c ^ (j + j) = 1 := by
      rw [h2, one_mul] at hij; exact hij
    exact ⟨by rw [two_mul]; exact (hna _).mp h2, by rw [two_mul]; exact (hnc _).mp h3⟩
  have heqa : ∀ k l : ℤ, (n : ℤ) ∣ k - l → a ^ k = a ^ l := fun k l hkl => by
    have h1 : a ^ (k - l) = 1 := (hna _).mpr hkl
    rw [zpow_sub, mul_inv_eq_one] at h1
    exact h1
  have heqc : ∀ k l : ℤ, (n : ℤ) ∣ k - l → c ^ k = c ^ l := fun k l hkl => by
    have h1 : c ^ (k - l) = 1 := (hnc _).mpr hkl
    rw [zpow_sub, mul_inv_eq_one] at h1
    exact h1
  have hzeq : z = a ^ (h : ℤ) * c ^ (h : ℤ) := by
    obtain ⟨i, j, hij | hij⟩ := key z hzP
    · have hzb := hzc b hbP
      have hconj : b * z * b⁻¹ = z := by rw [← hzb]; group
      have e1 : b * (a ^ i * c ^ j) * b⁻¹ = c ^ i * a ^ j := by
        calc b * (a ^ i * c ^ j) * b⁻¹ = (b * a ^ i * b⁻¹) * (b * c ^ j * b⁻¹) := by group
          _ = c ^ i * a ^ j := by rw [hbA, hbC]
      rw [hij, e1] at hconj
      have h1 : a ^ (i - j) = c ^ (i - j) := by
        have : a ^ (i - j) * (a ^ j * c ^ j) = c ^ (i - j) * (a ^ j * c ^ j) := by
          calc a ^ (i - j) * (a ^ j * c ^ j) = a ^ i * c ^ j := by
                rw [← mul_assoc, ← zpow_add]; simp
            _ = c ^ i * a ^ j := hconj.symm
            _ = c ^ (i - j) * (c ^ j * a ^ j) := by
                rw [← mul_assoc, ← zpow_add]; simp
            _ = c ^ (i - j) * (a ^ j * c ^ j) := by rw [hcomm j j]
        exact mul_right_cancel this
      have h2 : (n : ℤ) ∣ i - j := (hna _).mp (hdisj _ _ h1)
      obtain ⟨hi2, hj2⟩ := hsq i j (by rw [← hij]; exact hz2)
      obtain ⟨u, hu⟩ := hdiv2 i hi2
      obtain ⟨v, hv⟩ := hdiv2 j hj2
      have h3 : (2 : ℤ) ∣ u - v := by
        rw [← hpar, show h * (u - v) = i - j by rw [hu, hv]; ring]
        exact h2
      have h4 : ¬ ((2 : ℤ) ∣ u ∧ (2 : ℤ) ∣ v) := by
        rintro ⟨hu2, hv2⟩
        apply hz1
        rw [hij, (hna i).mpr (by rw [hu]; exact (hpar u).mpr hu2),
          (hnc j).mpr (by rw [hv]; exact (hpar v).mpr hv2), one_mul]
      have hu1 : (2 : ℤ) ∣ u - 1 := by
        rcases Int.even_or_odd u with ⟨w, hw⟩ | ⟨w, hw⟩
        · exfalso
          apply h4
          refine ⟨⟨w, by omega⟩, ⟨w, ?_⟩⟩
          obtain ⟨y, hy⟩ := h3
          omega
        · exact ⟨w, by omega⟩
      have hv1 : (2 : ℤ) ∣ v - 1 := by
        obtain ⟨y, hy⟩ := h3
        obtain ⟨w, hw⟩ := hu1
        exact ⟨w - y, by omega⟩
      rw [hij, heqa i h (by
        rw [show i - h = h * (u - 1) by rw [hu]; ring]; exact (hpar _).mpr hu1),
        heqc j h (by rw [show j - h = h * (v - 1) by rw [hv]; ring]; exact (hpar _).mpr hv1)]
    · exfalso
      have hc := hzc a haP
      have hba : b * a = c * b := by
        calc b * a = (b * a * b⁻¹) * b := by group
          _ = c * b := by rw [hbab]
      have hcomma : a * (a ^ i * c ^ j) = (a ^ i * c ^ j) * a := by
        have := hmul 1 0 i j
        have h' := hmul i j 1 0
        simp only [zpow_one, zpow_zero, mul_one] at this h'
        rw [this, h', add_comm 1 i, zero_add, add_zero]
      have h1 : (a ^ i * c ^ j) * (c * b) = (a ^ i * c ^ j) * (a * b) := by
        calc (a ^ i * c ^ j) * (c * b) = (a ^ i * c ^ j * b) * a := by
              rw [← hba]; group
          _ = z * a := by rw [hij]
          _ = a * z := hc
          _ = a * (a ^ i * c ^ j * b) := by rw [hij]
          _ = (a ^ i * c ^ j) * (a * b) := by rw [← mul_assoc, hcomma, mul_assoc]
      have h2 : c = a := by
        have := mul_left_cancel h1
        exact mul_right_cancel this
      have h3 : a ^ (1 : ℤ) = c ^ (1 : ℤ) := by simp [h2]
      have h4 := hdisj 1 1 h3
      rw [zpow_one] at h4
      have : orderOf a = 1 := by rw [h4]; exact orderOf_one
      omega
  obtain ⟨i, j, hij | hij⟩ := key t htP
  ·
    obtain ⟨hi2, hj2⟩ := hsq i j (by rw [← hij]; exact ht2)
    obtain ⟨u, hu⟩ := hdiv2 i hi2
    obtain ⟨v, hv⟩ := hdiv2 j hj2
    have h4 : ¬ ((2 : ℤ) ∣ u ∧ (2 : ℤ) ∣ v) := by
      rintro ⟨hu2, hv2⟩
      apply ht1
      rw [hij, (hna i).mpr (by rw [hu]; exact (hpar u).mpr hu2),
        (hnc j).mpr (by rw [hv]; exact (hpar v).mpr hv2), one_mul]
    have h5 : ¬ ((2 : ℤ) ∣ u - 1 ∧ (2 : ℤ) ∣ v - 1) := by
      rintro ⟨hu2, hv2⟩
      apply htz
      rw [hij, hzeq, heqa i h (by
        rw [show i - h = h * (u - 1) by rw [hu]; ring]; exact (hpar _).mpr hu2),
        heqc j h (by rw [show j - h = h * (v - 1) by rw [hv]; ring]; exact (hpar _).mpr hv2)]
    have h6 : (2 : ℤ) ∣ v - u - 1 := by
      rcases Int.even_or_odd u with ⟨w, hw⟩ | ⟨w, hw⟩ <;>
        rcases Int.even_or_odd v with ⟨y, hy⟩ | ⟨y, hy⟩
      · exfalso; exact h4 ⟨⟨w, by omega⟩, ⟨y, by omega⟩⟩
      · exact ⟨y - w, by omega⟩
      · exact ⟨y - w - 1, by omega⟩
      · exfalso; exact h5 ⟨⟨w, by omega⟩, ⟨y, by omega⟩⟩
    refine ⟨b, hbP, ?_⟩
    have e1 : b * (a ^ i * c ^ j) * b⁻¹ = c ^ i * a ^ j := by
      calc b * (a ^ i * c ^ j) * b⁻¹ = (b * a ^ i * b⁻¹) * (b * c ^ j * b⁻¹) := by group
        _ = c ^ i * a ^ j := by rw [hbA, hbC]
    rw [hij, e1, hzeq, hmul]
    have e2 : a ^ (j) = a ^ ((h : ℤ) + i) := heqa _ _ (by
      rw [show j - ((h : ℤ) + i) = h * (v - u - 1) by rw [hu, hv]; ring]
      exact (hpar _).mpr h6)
    have e3 : c ^ i = c ^ ((h : ℤ) + j) := heqc _ _ (by
      rw [show i - ((h : ℤ) + j) = h * (u - v - 1) by rw [hu, hv]; ring]
      refine (hpar _).mpr ?_
      obtain ⟨y, hy⟩ := h6
      exact ⟨-y - 1, by omega⟩)
    rw [← e2, ← e3]
    exact hcomm j i
  ·
    refine ⟨a ^ (h : ℤ), Subgroup.zpow_mem _ haP _, ?_⟩
    rw [hij, hzeq]
    calc a ^ (h : ℤ) * (a ^ i * c ^ j * b) * (a ^ (h : ℤ))⁻¹
        = a ^ (h : ℤ) * (a ^ i * c ^ j) * (b * a ^ (-(h : ℤ)) * b⁻¹) * b := by group
      _ = a ^ (h : ℤ) * (a ^ i * c ^ j) * c ^ (-(h : ℤ)) * b := by rw [hbA]
      _ = (a ^ (h : ℤ) * c ^ (h : ℤ)) * (a ^ i * c ^ j * b) := by
          have e1 : a ^ (h : ℤ) * (a ^ i * c ^ j) * c ^ (-(h : ℤ)) =
              a ^ ((h : ℤ) + i) * c ^ (j + -(h : ℤ)) := by
            have := hmul (h : ℤ) 0 i j
            simp only [zpow_zero, mul_one, zero_add] at this
            rw [this, mul_assoc, ← zpow_add]
          have e2 : (a ^ (h : ℤ) * c ^ (h : ℤ)) * (a ^ i * c ^ j) =
              a ^ ((h : ℤ) + i) * c ^ ((h : ℤ) + j) := hmul _ _ _ _
          have e3 : c ^ (j + -(h : ℤ)) = c ^ ((h : ℤ) + j) :=
            heqc _ _ ⟨-1, by rw [hnn]; ring⟩
          rw [← mul_assoc (a ^ (h : ℤ) * c ^ (h : ℤ)), e2, e1, e3]

end SD

end CFSG.ClassicalInvolution.Asc77
