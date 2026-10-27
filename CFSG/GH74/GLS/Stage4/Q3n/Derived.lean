module

public import CFSG.GH74.GLS.Stage4.Q3n.Setting

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open Subgroup

theorem mem_sup_iff_of_comm' {G : Type} [Group G] {K₁ K₂ : Subgroup G}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (x : G) :
    x ∈ K₁ ⊔ K₂ ↔ ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b}
        one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
          calc a * b * (a' * b') = a * (b * a') * b' := by group
            _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
            _ = a * a' * (b * b') := by group
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
          have := hcomm a ha b⁻¹ (K₂.inv_mem hb)
          calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
            _ = a⁻¹ * b⁻¹ := by
              have h1 : a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
              rw [h1, ← hcomm a ha b hb, mul_inv_rev] }
    have hle : K₁ ⊔ K₂ ≤ S := sup_le (fun a ha => ⟨a, ha, 1, K₂.one_mem, by simp⟩)
      (fun b hb => ⟨1, K₁.one_mem, b, hb, by simp⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem card_sup_of_comm_inf_bot {G : Type} [Group G] {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : A × B => (⟨(p.1 : G) * p.2,
    Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h' : a * b = a' * b' := congrArg Subtype.val h
    have h1 : a'⁻¹ * a ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem ha') ha, ?_⟩
      have : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
          _ = b' * b⁻¹ := by group
      rw [this]
      exact B.mul_mem hb' (B.inv_mem hb)
    rw [hinf, Subgroup.mem_bot] at h1
    have ha1 : a = a' := by
      have := congrArg (fun t => a' * t) h1
      simpa using this
    subst ha1
    have hb1 : b = b' := mul_left_cancel h'
    subst hb1
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm' hcomm x).1 hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩


namespace Q3nSetting

variable {G : Type} [Group G] [Finite G] {n : ℕ} (S : Q3nSetting G n)


theorem k_odd : Odd S.k := by
  have h1 := S.k_eq
  have h2 := S.q_mod
  rw [Int.ModEq] at h2
  generalize (3:ℤ)^n = t at h1 h2
  rcases S.ε_pm with h | h <;> rw [h] at h1 h2 <;> (rw [Nat.odd_iff]; omega)

theorem k_ge (hn : 3 ≤ n) : 13 ≤ S.k := by
  have h1 := S.k_eq
  have h3 : (27 : ℤ) ≤ 3 ^ n := by
    calc (27 : ℤ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  generalize (3:ℤ)^n = t at h1 h3
  rcases S.ε_pm with h | h <;> rw [h] at h1 <;> omega

theorem three_not_dvd_k (hn : 1 ≤ n) : ¬ 3 ∣ S.k := by
  intro hdvd
  have h1 := S.k_eq
  have h3 : (3 : ℤ) ∣ 3 ^ n := dvd_pow_self 3 (by omega)
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨d, hd⟩ := h3
  rcases S.ε_pm with h | h <;> rw [h] at h1 <;> (generalize (3:ℤ)^n = t at h1 hd; omega)


theorem Q_card_odd : Odd (Nat.card S.Q) := by
  rw [S.Q_card]
  exact S.k_odd.pow

theorem odd_of_mem_Q : ∀ x ∈ S.Q, Odd (orderOf x) := by
  intro x hx
  exact Odd.of_dvd_nat S.Q_card_odd (Subgroup.orderOf_dvd_natCard S.Q hx)

theorem exists_mul_of_mem_H : ∀ h ∈ S.H, ∃ u ∈ S.U, ∃ q ∈ S.Q, h = u * q := by
  intro h hh
  have hcomm : ∀ x ∈ S.U, ∀ y ∈ S.Q, x * y = y * x :=
    fun x hx y hy => S.H_comm x (S.U_le_H hx) y (S.Q_le_H hy)
  rw [S.H_eq] at hh
  exact (mem_sup_iff_of_comm' hcomm h).1 hh

theorem card_H : Nat.card S.H = 4 * S.k ^ 2 := by
  have hcomm : ∀ x ∈ S.U, ∀ y ∈ S.Q, x * y = y * x :=
    fun x hx y hy => S.H_comm x (S.U_le_H hx) y (S.Q_le_H hy)
  have := card_sup_of_comm_inf_bot hcomm S.U_inf_Q
  rw [← S.H_eq, S.U_card, S.Q_card] at this
  exact this

theorem odd_mem_Q : ∀ h ∈ S.H, Odd (orderOf h) → h ∈ S.Q := by
  intro h hh hodd
  obtain ⟨u, hu, q, hq, rfl⟩ := S.exists_mul_of_mem_H h hh
  have hcomm : u * q = q * u := S.H_comm u (S.U_le_H hu) q (S.Q_le_H hq)
  have hqN : q ^ Nat.card S.Q = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard S.Q hq)
  obtain ⟨m, hm⟩ := S.Q_card_odd
  have huu : u ^ Nat.card S.Q = u := by
    rw [hm, pow_succ, pow_mul, show u ^ 2 = 1 by rw [pow_two]; exact S.U_exp u hu, one_pow, one_mul]
  have hpow : (u * q) ^ Nat.card S.Q = u := by
    rw [(show Commute u q from hcomm).mul_pow, huu, hqN, mul_one]
  have hdvd : orderOf u ∣ orderOf (u * q) := by
    have := orderOf_pow_dvd (x := u * q) (Nat.card S.Q)
    rwa [hpow] at this
  have hu2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact S.U_exp u hu)
  have hodd' : Odd (orderOf u) := Odd.of_dvd_nat hodd hdvd
  have h1 : orderOf u = 1 := by
    have := Nat.le_of_dvd (by norm_num) hu2
    rcases hodd' with ⟨j, hj⟩
    interval_cases hj' : orderOf u <;> omega
  have hu1 : u = 1 := orderOf_eq_one_iff.1 h1
  rw [hu1, one_mul]
  exact hq

theorem exists_ne_one_Q (hk : 2 ≤ S.k) : ∃ q ∈ S.Q, q ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : S.Q = ⊥ := (Subgroup.eq_bot_iff_forall S.Q).2 hcon
  have h1 : Nat.card S.Q = 1 := by rw [this]; simp
  rw [S.Q_card] at h1
  have : 2 ^ 2 ≤ S.k ^ 2 := Nat.pow_le_pow_left hk 2
  omega

theorem w₀_not_mem_H (hk : 2 ≤ S.k) : S.w₀ ∉ S.H := by
  intro hw
  obtain ⟨q, hq, hq1⟩ := S.exists_ne_one_Q hk
  have h1 := S.w₀_inv q (S.Q_le_H hq)
  have h2 : S.w₀ * q * S.w₀⁻¹ = q := by
    rw [S.H_comm S.w₀ hw q (S.Q_le_H hq)]; group
  rw [h2] at h1
  have hsq : q * q = 1 := by
    calc q * q = q * q⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel q
  have hdvd : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hodd := S.odd_of_mem_Q q hq
  have h1' : orderOf q = 1 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    rcases hodd with ⟨j, hj⟩
    interval_cases hj' : orderOf q <;> omega
  exact hq1 (orderOf_eq_one_iff.1 h1')

theorem H_le_centralizer : S.H ≤ Subgroup.centralizer (S.U : Set G) := by
  intro h hh
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact S.H_comm u (S.U_le_H hu) h hh

theorem w₀_mem_centralizer : S.w₀ ∈ Subgroup.centralizer (S.U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (S.w₀_cent u hu).symm

theorem W_conj_Q : ∀ w ∈ S.W, ∀ q ∈ S.Q, w * q * w⁻¹ ∈ S.Q := by
  intro w hw q hq
  have hH := S.N_norm_H w (S.W_norm_U w hw) q (S.Q_le_H hq)
  apply S.odd_mem_Q _ hH
  have hpow : (w * q * w⁻¹) ^ Nat.card S.Q = 1 := by
    rw [show w * q * w⁻¹ = (MulAut.conj w) q from rfl, ← map_pow,
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard S.Q hq)]
    simp
  exact Odd.of_dvd_nat S.Q_card_odd (orderOf_dvd_iff_pow_eq_one.2 hpow)

end Q3nSetting

end CFSG.GH74.GLS.Stage4.Q3n
