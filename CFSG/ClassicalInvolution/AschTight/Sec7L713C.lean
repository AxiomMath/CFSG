module

public import CFSG.ClassicalInvolution.Asc77.AscIHSL2
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem s3_cases {Q : Type*} [Group Q] {x y : Q} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) ^ 3 = 1) {g : Q} (hg : g ∈ Subgroup.closure ({x, y} : Set Q)) :
    g = 1 ∨ g = x ∨ g = y ∨ g = x * y ∨ g = y * x ∨ g = x * y * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hbraid : y * x * y = x * y * x := by
    have h1 : x * y * x * (y * x * y) = 1 := by
      rw [pow_three] at hxy
      calc x * y * x * (y * x * y) = x * y * (x * y * (x * y)) := by group
        _ = 1 := hxy
    calc y * x * y = (x * y * x)⁻¹ * (x * y * x * (y * x * y)) := by group
      _ = (x * y * x)⁻¹ := by rw [h1, mul_one]
      _ = x⁻¹ * y⁻¹ * x⁻¹ := by group
      _ = x * y * x := by rw [hxi, hyi]
  set S : Set Q := {g | g = 1 ∨ g = x ∨ g = y ∨ g = x * y ∨ g = y * x ∨ g = x * y * x}
    with hS
  have hxS : ∀ w ∈ S, x * w ∈ S := by
    rintro w (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one x))
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [← mul_assoc, hx, one_mul]
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      rw [mul_assoc]
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      rw [← mul_assoc, ← mul_assoc, hx, one_mul]
  have hyS : ∀ w ∈ S, y * w ∈ S := by
    rintro w (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl (mul_one y)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inl hy
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      rw [← mul_assoc, hbraid]
    · refine Or.inr (Or.inl ?_)
      rw [← mul_assoc, hy, one_mul]
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      calc y * (x * y * x) = y * x * y * x := by group
        _ = x * y * x * x := by rw [hbraid]
        _ = x * y := by rw [mul_assoc, hx, mul_one]
  have hmem : g ∈ S := by
    induction hg using Subgroup.closure_induction_left with
    | one => exact Or.inl rfl
    | mul_left s hs w _ ih =>
      rcases hs with rfl | rfl
      · exact hxS w ih
      · exact hyS w ih
    | inv_mul_cancel s hs w _ ih =>
      rcases hs with rfl | rfl
      · rw [hxi]
        exact hxS w ih
      · rw [hyi]
        exact hyS w ih
  exact hmem

theorem mem_or_mul_inv_mem_of_relIndex_two {A R : Subgroup G} (h2 : A.relIndex R = 2) {x y : G}
    (hx : x ∈ R) (hxA : x ∉ A) (hy : y ∈ R) : y ∈ A ∨ y * x⁻¹ ∈ A := by
  have hidx : (A.subgroupOf R).index = 2 := h2
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨y, hy⟩ : ↥R))
    (b := (⟨x, hx⟩ : ↥R)⁻¹)
  rw [inv_mem_iff] at key
  by_cases hyA : y ∈ A
  · exact Or.inl hyA
  · right
    have hxA' : (⟨x, hx⟩ : ↥R) ∉ A.subgroupOf R := fun h => hxA (Subgroup.mem_subgroupOf.mp h)
    have hyA' : (⟨y, hy⟩ : ↥R) ∉ A.subgroupOf R := fun h => hyA (Subgroup.mem_subgroupOf.mp h)
    have h1 : (⟨y, hy⟩ : ↥R) * (⟨x, hx⟩ : ↥R)⁻¹ ∈ A.subgroupOf R := key.mpr (iff_of_false hyA' hxA')
    exact Subgroup.mem_subgroupOf.mp h1

theorem mul_self_mem_of_relIndex_two {A R : Subgroup G} (h2 : A.relIndex R = 2) {x : G}
    (hx : x ∈ R) : x * x ∈ A := by
  have hidx : (A.subgroupOf R).index = 2 := h2
  exact Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hidx ⟨x, hx⟩)

theorem relIndex_eq_two_of_card [Finite G] {A R : Subgroup G} (hAR : A ≤ R)
    (hcard : Nat.card R = 2 * Nat.card A) : A.relIndex R = 2 := by
  have h1 := Subgroup.relIndex_mul_card A R
  rw [inf_eq_left.mpr hAR, hcard] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

theorem isCoprime_two_pow_of_odd {f : ℤ} (hf : Odd f) (n : ℕ) : IsCoprime f (2 ^ n) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have h1 : Nat.Coprime f.natAbs 2 := (Nat.coprime_two_right).mpr (Int.natAbs_odd.mpr hf)
  have h2 : Nat.Coprime f.natAbs (2 ^ n) := Nat.Coprime.pow_right n h1
  simpa [Int.gcd, Int.natAbs_pow] using h2

theorem exists_fixed_of_even {v t a : G} {k : ℕ} (hk : 2 ≤ k) (hv : orderOf v = 2 ^ k)
    (htv : t * v * t⁻¹ = v⁻¹) (ht2 : t * t = v ^ (2 ^ (k - 1))) (ha2 : a * a = 1) {e m : ℤ}
    (hae : a * v * a⁻¹ = v ^ e) (ham : a * t * a⁻¹ = v ^ m * t) (hm : Even m) :
    ∃ g : G, a * g * a⁻¹ = g ∧ orderOf g = 4 ∧ g ∈ Subgroup.closure ({v, t} : Set G) := by
  have hconj : ∀ n : ℤ, a * v ^ n * a⁻¹ = v ^ (e * n) := fun n => by
    rw [← conj_zpow, hae, ← zpow_mul]
  have hord : ∀ n : ℤ, v ^ n = 1 ↔ (2 : ℤ) ^ k ∣ n := fun n => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hv]
    push_cast
    rfl
  have he2 : (2 : ℤ) ^ k ∣ e * e - 1 := by
    have h1 : a * (a * v * a⁻¹) * a⁻¹ = v := by
      calc a * (a * v * a⁻¹) * a⁻¹ = (a * a) * v * (a * a)⁻¹ := by group
        _ = v := by rw [ha2]; group
    rw [hae, hconj] at h1
    refine (hord _).mp ?_
    rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  have h4 : (4 : ℤ) ∣ 2 ^ (2 + k') := ⟨2 ^ k', by ring⟩
  have heodd : Odd e := by
    rw [← Int.not_even_iff_odd]
    intro hev
    have h2 : (2 : ℤ) ∣ e * e - 1 := (dvd_trans ⟨2, by norm_num⟩ h4).trans he2
    have h3 : Even (e * e) := Int.even_mul.mpr (Or.inl hev)
    exact (Int.not_even_iff_odd.mpr (h3.sub_odd odd_one)) (even_iff_two_dvd.mpr h2)
  have hk1 : 2 + k' - 1 = k' + 1 := by omega
  have hk2 : 2 + k' - 2 = k' := by omega
  by_cases h4e : (4 : ℤ) ∣ e - 1
  · refine ⟨v ^ (2 ^ k'), ?_, ?_, Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _⟩
    · have h1 := hconj ((2 : ℤ) ^ k')
      rw [show ((2 : ℤ) ^ k') = ((2 ^ k' : ℕ) : ℤ) by push_cast; rfl, zpow_natCast] at h1
      rw [h1]
      rw [show v ^ (2 ^ k') = v ^ (((2 ^ k' : ℕ) : ℤ)) by rw [zpow_natCast]]
      rw [← mul_inv_eq_one, ← zpow_sub]
      refine (hord _).mpr ?_
      obtain ⟨c, hc⟩ := h4e
      refine ⟨c, ?_⟩
      push_cast
      have : e * 2 ^ k' - 2 ^ k' = (e - 1) * 2 ^ k' := by ring
      rw [this, hc]
      ring
    · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨4, by rw [hv]; ring⟩, hv]
      rw [show 2 ^ (2 + k') = 2 ^ k' * 4 by ring]
      exact Nat.mul_div_cancel_left 4 (pow_pos two_pos k')
  · obtain ⟨f, hf⟩ : ∃ f : ℤ, e - 1 = 2 * f := by
      obtain ⟨c, hc⟩ := heodd
      exact ⟨c, by omega⟩
    have hfodd : Odd f := by
      rw [← Int.not_even_iff_odd]
      rintro ⟨d, hd⟩
      exact h4e ⟨d, by omega⟩
    obtain ⟨m', hm'⟩ := hm
    obtain ⟨α, β, hαβ⟩ := isCoprime_two_pow_of_odd hfodd (k' + 1)
    set i : ℤ := -m' * α with hi
    refine ⟨v ^ i * t, ?_, ?_, Subgroup.mul_mem _
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.subset_closure (by simp))⟩
    · have h1 : a * (v ^ i * t) * a⁻¹ = v ^ (e * i + m) * t := by
        calc a * (v ^ i * t) * a⁻¹ = (a * v ^ i * a⁻¹) * (a * t * a⁻¹) := by group
          _ = v ^ (e * i) * (v ^ m * t) := by rw [hconj, ham]
          _ = v ^ (e * i + m) * t := by rw [zpow_add]; group
      rw [h1]
      congr 1
      rw [← mul_inv_eq_one, ← zpow_sub]
      refine (hord _).mpr ⟨m' * β, ?_⟩
      rw [hm', hi]
      have : e * (-m' * α) + (m' + m') - -m' * α = m' * (2 - (e - 1) * α) := by ring
      rw [this, hf]
      have h2 : 2 - 2 * f * α = 2 * (1 - α * f) := by ring
      rw [h2, show (1 : ℤ) - α * f = β * 2 ^ (k' + 1) by linarith]
      ring
    · have hsq : (v ^ i * t) * (v ^ i * t) = v ^ (2 ^ (k' + 1)) := by
        have htvi : t * v ^ i * t⁻¹ = v ^ (-i) := by
          rw [← conj_zpow, htv, inv_zpow']
        calc (v ^ i * t) * (v ^ i * t) = v ^ i * (t * v ^ i * t⁻¹) * (t * t) := by group
          _ = v ^ (2 ^ (k' + 1)) := by
            rw [htvi, ht2, hk1, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      have hne : ¬ (v ^ i * t) ^ 2 ^ 1 = 1 := by
        rw [pow_one, pow_two, hsq]
        intro h
        have := orderOf_dvd_of_pow_eq_one h
        rw [hv] at this
        have h3 := Nat.le_of_dvd (pow_pos two_pos _) this
        have h5 : 2 ^ (k' + 1) < 2 ^ (2 + k') := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have hone : (v ^ i * t) ^ 2 ^ (1 + 1) = 1 := by
        have h2 : (v ^ i * t) ^ 2 = v ^ (2 ^ (k' + 1)) := by rw [pow_two, hsq]
        rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h2, ← pow_mul,
          show 2 ^ (k' + 1) * 2 = 2 ^ (2 + k') by ring, ← hv, pow_orderOf_eq_one]
      exact orderOf_eq_prime_pow hne hone

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
