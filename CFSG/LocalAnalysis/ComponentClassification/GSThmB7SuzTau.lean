module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512b
public import CFSG.Walter.W67.Section5.MaxClass
public import CFSG.GH74.Uniqueness.SU.SU1MaxClassShape

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace SuzTau

variable {P : Type} [Group P] [Finite P]

omit [Finite P] in
theorem centralizer_eq_top {p r b : P} (hcl : closure {p, r} = (⊤ : Subgroup P))
    (hp : b * p = p * b) (hr : b * r = r * b) : centralizer ({b} : Set P) = ⊤ := by
  rw [eq_top_iff, ← hcl, closure_le]
  intro w hw
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  rcases hw with rfl | rfl
  · exact hp.symm
  · exact hr.symm

omit [Finite P] in
theorem card_centralizer_of_eq_top {b : P} (h : centralizer ({b} : Set P) = ⊤) :
    Nat.card (centralizer ({b} : Set P)) = Nat.card P := by
  rw [h, card_top]

theorem exists_dihedral_of_card_eight (h8 : Nat.card P = 8) {b : P} (hb : orderOf b = 2)
    (hc : Nat.card (centralizer ({b} : Set P)) = 4) :
    ∃ p : P, closure {p, b} = ⊤ ∧ 2 * orderOf p = Nat.card P ∧ b * p * b⁻¹ = p⁻¹ := by
  classical
  have hnab : ¬ ∀ x y : P, x * y = y * x := by
    intro hall
    have h1 : centralizer ({b} : Set P) = ⊤ :=
      eq_top_iff.mpr fun w _ => mem_centralizer_singleton_iff.mpr (hall w b)
    rw [card_centralizer_of_eq_top h1, h8] at hc
    exact absurd hc (by norm_num)
  obtain ⟨p, hp4⟩ : ∃ p : P, orderOf p = 4 := by
    by_contra hno
    push Not at hno
    apply hnab
    have hdvd : ∀ x : P, orderOf x ∣ 2 ^ 3 := fun x => by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h8]
      exact orderOf_dvd_natCard x
    by_cases h8' : ∃ x : P, orderOf x = 8
    · obtain ⟨x, hx⟩ := h8'
      have htop : zpowers x = ⊤ := by
        apply eq_top_of_card_eq
        rw [Nat.card_zpowers, hx, h8]
      intro u v
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (htop ▸ mem_top u : u ∈ zpowers x)
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (htop ▸ mem_top v : v ∈ zpowers x)
      exact (Commute.zpow_zpow_self x i j).eq
    · push Not at h8'
      have hsq : ∀ x : P, x * x = 1 := by
        intro x
        obtain ⟨k, hk, hxk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hdvd x)
        interval_cases k
        · rw [pow_zero, orderOf_eq_one_iff] at hxk
          rw [hxk, one_mul]
        · rw [← pow_two, ← pow_one 2, ← hxk, pow_orderOf_eq_one]
        · exact absurd hxk (by simpa using hno x)
        · exact absurd hxk (by simpa using h8' x)
      intro u v
      have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u)
      have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v)
      calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq (u * v))).symm
        _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
        _ = v * u := by rw [hu, hv]
  have hidx : (zpowers p).index = 2 := by
    have h1 := card_mul_index (zpowers p)
    rw [Nat.card_zpowers, hp4, h8] at h1
    omega
  have hnorm : (zpowers p).Normal := normal_of_index_eq_two hidx
  have hp2c : ∀ g : P, g * p ^ 2 = p ^ 2 * g := by
    intro g
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hnorm.conj_mem p (mem_zpowers p) g)
    have hk4 : orderOf (g * p * g⁻¹) = 4 := by
      rw [show g * p * g⁻¹ = (MulAut.conj g) p by rw [MulAut.conj_apply], MulEquiv.orderOf_eq,
        hp4]
    have hp44 : p ^ (4 : ℤ) = 1 := by rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num,
      zpow_natCast, ← hp4, pow_orderOf_eq_one]
    have hkodd : Odd k := by
      by_contra hev
      obtain ⟨j, rfl⟩ := Int.not_odd_iff_even.mp hev
      have h2 : (g * p * g⁻¹) ^ 2 = 1 := by
        rw [← hk, ← zpow_natCast, ← zpow_mul, show (j + j) * ((2 : ℕ) : ℤ) = 4 * j by
          push_cast; ring, zpow_mul, hp44, one_zpow]
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hk4] at this
      exact absurd this (by norm_num)
    obtain ⟨j, rfl⟩ := hkodd
    have h3 : g * p ^ 2 * g⁻¹ = p ^ 2 := by
      rw [← conj_pow, ← hk, ← zpow_natCast, ← zpow_mul,
        show (2 * j + 1) * ((2 : ℕ) : ℤ) = 4 * j + 2 by push_cast; ring, zpow_add, zpow_mul,
        hp44, one_zpow, one_mul]
      norm_cast
    calc g * p ^ 2 = (g * p ^ 2 * g⁻¹) * g := by group
      _ = p ^ 2 * g := by rw [h3]
  have hbp : b ∉ zpowers p := by
    intro hbz
    have hbsq : b ^ 2 = 1 := by rw [← hb, pow_orderOf_eq_one]
    have h2 : orderOf (p ^ 2) = 2 := by
      rw [orderOf_pow' p (by norm_num), hp4]
      norm_num
    have h3 := mem_zpowers_half_of_sq_eq_one (c := p) (by rw [hp4]; norm_num) hbz hbsq
    rw [hp4] at h3
    have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
    have h4 : b = p ^ 2 := eq_of_mem_zpowers_of_orderOf_eq_two h2 h3 hb1
    have h5 : centralizer ({b} : Set P) = ⊤ :=
      eq_top_iff.mpr fun g _ => mem_centralizer_singleton_iff.mpr (h4 ▸ hp2c g)
    rw [card_centralizer_of_eq_top h5, h8] at hc
    exact absurd hc (by norm_num)
  have hcl : closure {p, b} = ⊤ := CFSG.GH74.Uniqueness.SU.SU1.closure_pair_eq_top hidx hbp
  refine ⟨p, hcl, by rw [hp4, h8], ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hnorm.conj_mem p (mem_zpowers p) b)
  have hk4 : orderOf (b * p * b⁻¹) = 4 := by
    rw [show b * p * b⁻¹ = (MulAut.conj b) p by rw [MulAut.conj_apply], MulEquiv.orderOf_eq, hp4]
  have hk' : p ^ (k % (4 : ℤ)) = b * p * b⁻¹ := by
    rw [← hk]
    have h1 := zpow_mod_orderOf p k
    rw [hp4] at h1
    exact_mod_cast h1
  have hp44 : p ^ 4 = 1 := by rw [← hp4, pow_orderOf_eq_one]
  have hmod : k % (4 : ℤ) = 0 ∨ k % (4 : ℤ) = 1 ∨ k % (4 : ℤ) = 2 ∨ k % (4 : ℤ) = 3 := by
    omega
  rcases hmod with h0 | h1 | h2 | h3
  · rw [h0, zpow_zero] at hk'
    rw [← hk', orderOf_one] at hk4
    exact absurd hk4 (by norm_num)
  · exfalso
    rw [h1, zpow_one] at hk'
    have hbpc : b * p = p * b := by
      calc b * p = (b * p * b⁻¹) * b := by group
        _ = p * b := by rw [← hk']
    have h5 := centralizer_eq_top hcl hbpc (Commute.refl b).eq
    rw [card_centralizer_of_eq_top h5, h8] at hc
    exact absurd hc (by norm_num)
  · exfalso
    rw [h2] at hk'
    have h6 : (b * p * b⁻¹) ^ 2 = 1 := by
      rw [← hk', ← zpow_natCast, ← zpow_mul]
      norm_num
      exact hp44
    have := orderOf_dvd_of_pow_eq_one h6
    rw [hk4] at this
    exact absurd this (by norm_num)
  · rw [h3] at hk'
    rw [← hk', show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hp44]

end SuzTau

theorem suzukiTausskyInput : SuzukiTausskyInput := by
  intro P _ _ hP h8 b hb hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm2, hm, hγ⟩ := CFSG.Walter.W67.isMaximalClass_of_card_centralizer hP b hb
    (by rw [hc]; norm_num)
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  ·
    have h8' : Nat.card P = 8 := by rw [hm, show m = 3 by omega]; norm_num
    obtain ⟨p, hcl, hcard, hrel⟩ := SuzTau.exists_dihedral_of_card_eight h8' hb hc
    exact ⟨p, b, hcl, hcard, by rw [← hb, pow_orderOf_eq_one], Or.inl hrel⟩
  ·
    have hnil : Group.IsNilpotent P := hP.isNilpotent
    have hcl : m - 1 ≤ Group.nilpotencyClass P := by
      by_contra hcon
      apply hγ
      rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
      omega
    obtain ⟨a, y, ha, hy, hgen, hD | hQ | hSD⟩ :=
      CFSG.GH74.Uniqueness.SU.SU1.exists_shape_of_maxClass hm4 hm hcl
    · refine ⟨a, y, hgen, ?_, by rw [pow_two]; exact hD.1, Or.inl hD.2⟩
      rw [ha, hm, ← pow_succ']
      congr 1
      omega
    ·
      exfalso
      have haP : a ∈ (⊤ : Subgroup P) := mem_top a
      have hc2 : 2 * orderOf a = Nat.card (⊤ : Subgroup P) := by
        rw [card_top, ha, hm, ← pow_succ']
        congr 1
        omega
      have hbsq : b ^ 2 = 1 := by rw [← hb, pow_orderOf_eq_one]
      have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
      have hhalf : orderOf a / 2 = 2 ^ (m - 2) := by
        rw [ha, show m - 1 = (m - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      have h2a : 2 ∣ orderOf a := ⟨2 ^ (m - 2), by
        rw [ha, show m - 1 = (m - 2) + 1 by omega, pow_succ, mul_comm]⟩
      have hord : orderOf (a ^ (2 ^ (m - 2))) = 2 := by
        rw [orderOf_pow_of_dvd (by positivity) (by rw [ha]; exact Nat.pow_dvd_pow 2 (by omega)),
          ha, Nat.pow_div (by omega) (by norm_num), show m - 1 - (m - 2) = 1 by omega, pow_one]
      rcases mem_presentation_cases haP (mem_top y) hgen hc2 (mem_top b) with hbz | hbz
      ·
        have h3 := mem_zpowers_half_of_sq_eq_one h2a hbz hbsq
        rw [hhalf] at h3
        have h4 : b = a ^ (2 ^ (m - 2)) := eq_of_mem_zpowers_of_orderOf_eq_two hord h3 hb1
        have h5 : centralizer ({b} : Set P) = ⊤ := by
          refine SuzTau.centralizer_eq_top hgen ?_ ?_
          · rw [h4, ← pow_succ, ← pow_succ']
          · rw [h4, ← hQ.1, mul_assoc]
        rw [SuzTau.card_centralizer_of_eq_top h5, hm] at hc
        have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
        omega
      ·
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hbz
        have hbk : b = y * a ^ k := by rw [hk]; group
        have hsq : b ^ 2 = a ^ (2 ^ (m - 2)) := by
          have hyak : y * a ^ k * y⁻¹ = a ^ (-k) := by
            rw [← conj_zpow, hQ.2, inv_zpow, zpow_neg]
          calc b ^ 2 = (y * a ^ k * y⁻¹) * (y * y) * a ^ k := by rw [hbk, pow_two]; group
            _ = a ^ (-k) * a ^ (2 ^ (m - 2)) * a ^ k := by rw [hyak, hQ.1]
            _ = a ^ (2 ^ (m - 2)) := by
              rw [mul_assoc, ← zpow_natCast a (2 ^ (m - 2)),
                (Commute.zpow_zpow_self a ((2 ^ (m - 2) : ℕ) : ℤ) k).eq, ← mul_assoc,
                ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
        rw [hsq] at hbsq
        have h7 := orderOf_dvd_of_pow_eq_one hbsq
        rw [ha] at h7
        have h8 := Nat.le_of_dvd (by positivity) h7
        have h9 : 2 ^ (m - 2) < 2 ^ (m - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
    · refine ⟨a, y, hgen, ?_, by rw [pow_two]; exact hSD.1, Or.inr ?_⟩
      · rw [ha, hm, ← pow_succ']
        congr 1
        omega
      · rw [hSD.2, ha, show m - 1 = (m - 2) + 1 by omega, pow_succ,
          Nat.mul_div_cancel _ (by norm_num)]

end CFSG.ComponentClassification.GSThmB
