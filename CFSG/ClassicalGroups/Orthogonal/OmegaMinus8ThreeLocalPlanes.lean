module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open Module QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {b c : K}

@[expose] def minusPi (q : ℕ) : ℕ := if q % 3 = 1 then q - 1 else q + 1

@[expose] def plusPi (q : ℕ) : ℕ := if q % 3 = 1 then q + 1 else q - 1

private theorem minusPi_ne_zero {q : ℕ} (hq : 2 ≤ q) : minusPi q ≠ 0 := by
  rw [minusPi]; split_ifs <;> omega

private theorem plusPi_ne_zero {q : ℕ} (hq : 2 ≤ q) : plusPi q ≠ 0 := by
  rw [plusPi]; split_ifs <;> omega

theorem natCard_orthogonalGroup_rotForm [Finite K] (h3 : (3 : K) ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) = 2 * minusPi (Nat.card K) := by
  have htype : IsPlusType (rotForm K) ↔ Nat.card K % 3 = 1 :=
    (isPlusType_rotForm_iff h3).trans (isSplit_iff_card_mod_three h3)
  have hcard := natCard_orthogonalGroup_of_type (V := K × K) (Q := rotForm K)
    (nondegenerate_polarBilin_rotForm h3) (m := 0) (by simp [Module.finrank_prod])
    (ε := if Nat.card K % 3 = 1 then (1 : ℤ) else -1) (by
      by_cases h : Nat.card K % 3 = 1
      · exact Or.inl ⟨by simp [h], htype.mpr h⟩
      · exact Or.inr ⟨by simp [h], fun hp => h (htype.mp hp)⟩)
  rw [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.prod_empty] at hcard
  simp only [Nat.zero_mul, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul] at hcard
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [minusPi]
  split_ifs with h
  · rw [if_pos h] at hcard
    omega
  · rw [if_neg h] at hcard
    omega

theorem natCard_orthogonalGroup_wForm [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (wForm b c)) = 2 * plusPi (Nat.card K) := by
  have htype : IsPlusType (wForm b c) ↔ ¬ Nat.card K % 3 = 1 :=
    (isPlusType_wForm_iff hbc).trans (not_congr (isSplit_iff_card_mod_three h3))
  have hcard := natCard_orthogonalGroup_of_type (V := K × K) (Q := wForm b c)
    (nondegenerate_polarBilin_wForm hbc) (m := 0) (by simp [Module.finrank_prod])
    (ε := if Nat.card K % 3 = 1 then (-1 : ℤ) else 1) (by
      by_cases h : Nat.card K % 3 = 1
      · exact Or.inr ⟨by simp [h], fun hp => (htype.mp hp) h⟩
      · exact Or.inl ⟨by simp [h], htype.mpr h⟩)
  rw [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.prod_empty] at hcard
  simp only [Nat.zero_mul, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul] at hcard
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [plusPi]
  split_ifs with h
  · rw [if_pos h] at hcard
    omega
  · rw [if_neg h] at hcard
    omega

theorem exists_orderOf_eq_mem_orthogonalGroup_rotForm [Finite K] (h3 : (3 : K) ≠ 0) {p : ℕ}
    (hp : p.Prime) (hpd : p ∣ minusPi (Nat.card K)) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K), orderOf g = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) =
      2 * minusPi (Nat.card K) := natCard_orthogonalGroup_rotForm h3
  have hne : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) ≠ 0 := by
    rw [hcard]
    exact Nat.mul_ne_zero (by norm_num) (minusPi_ne_zero hq)
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) :=
    Nat.finite_of_card_ne_zero hne
  have hdvd : p ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) := by
    rw [hcard]
    exact dvd_mul_of_dvd_right hpd 2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(TauCeti.QuadraticMap.orthogonalGroup (rotForm K))) p hdvd
  exact ⟨(x : (K × K) ≃ₗ[K] (K × K)), x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem exists_orderOf_eq_mem_orthogonalGroup_wForm [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ plusPi (Nat.card K)) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (wForm b c), orderOf g = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (wForm b c)) =
      2 * plusPi (Nat.card K) := natCard_orthogonalGroup_wForm h3 hbc
  have hne : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (wForm b c)) ≠ 0 := by
    rw [hcard]
    exact Nat.mul_ne_zero (by norm_num) (plusPi_ne_zero hq)
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup (wForm b c)) :=
    Nat.finite_of_card_ne_zero hne
  have hdvd : p ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (wForm b c)) := by
    rw [hcard]
    exact dvd_mul_of_dvd_right hpd 2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(TauCeti.QuadraticMap.orthogonalGroup (wForm b c))) p hdvd
  exact ⟨(x : (K × K) ≃ₗ[K] (K × K)), x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem rotLE_sq_add (p : K × K) : rotLE K (rotLE K p) + rotLE K p + p = 0 := by
  refine Prod.ext ?_ ?_ <;> simp [rotLE] <;> ring

theorem rotLE_mem_orthogonalGroup :
    rotLE K ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr rotForm_rotLE

theorem eq_rotLE_or_eq_inv_of_isometry (h3 : (3 : K) ≠ 0) {σ : (K × K) ≃ₗ[K] (K × K)}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K))
    (hrel : ∀ p : K × K, σ (σ p) + σ p + p = 0) : σ = rotLE K ∨ σ = (rotLE K)⁻¹ := by
  have hQ : ∀ p, rotForm K (σ p) = rotForm K p := fun p =>
    CFSG.ClassicalGroups.Orthogonal.map_of_mem hσ p
  obtain ⟨a, c, ha⟩ : ∃ a c : K, σ (1, 0) = (a, c) := ⟨_, _, rfl⟩
  obtain ⟨b, d, hb⟩ : ∃ b d : K, σ (0, 1) = (b, d) := ⟨_, _, rfl⟩
  have hxy : ∀ x y : K, σ (x, y) = (a * x + b * y, c * x + d * y) := by
    intro x y
    have h : ((x, y) : K × K) = x • ((1 : K), (0 : K)) + y • ((0 : K), (1 : K)) := by
      ext <;> simp
    rw [h, map_add, map_smul, map_smul, ha, hb]
    ext <;> simp <;> ring
  have E1 := hQ (1, 0)
  have E2 := hQ (0, 1)
  rw [ha, rotForm_apply, rotForm_apply] at E1
  rw [hb, rotForm_apply, rotForm_apply] at E2
  have R1 := hrel (1, 0)
  have R2 := hrel (0, 1)
  rw [ha, hxy] at R1
  rw [hb, hxy] at R2
  simp only [Prod.mk_add_mk, Prod.mk_eq_zero, mul_one, mul_zero, add_zero, zero_add] at R1 R2
  obtain ⟨R1a, R3⟩ := R1
  obtain ⟨R2a, R4⟩ := R2
  have hS : ∀ p : K × K, rotForm K (σ p + p) = rotForm K p := fun p => by
    have h : σ p + p = -σ (σ p) := by
      have := hrel p
      linear_combination this
    rw [h, QuadraticMap.map_neg, hQ, hQ]
  have S1 := hS (1, 0)
  have S2 := hS (0, 1)
  rw [ha, Prod.mk_add_mk, rotForm_apply, rotForm_apply] at S1
  rw [hb, Prod.mk_add_mk, rotForm_apply, rotForm_apply] at S2
  simp only [add_zero, zero_add] at S1 S2
  simp only [one_pow, zero_pow two_ne_zero, mul_zero, mul_one, sub_zero, zero_sub, add_zero,
    zero_add] at E1 E2 S1 S2
  have hc : c = 2 * a + 1 := by linear_combination E1 - S1
  have hb' : b = 2 * d + 1 := by linear_combination E2 - S2
  have ht : a + d + 1 = 0 := by
    by_contra ht
    have hb0 : b = 0 := by
      have : b * (a + d + 1) = 0 := by linear_combination R2a
      exact (mul_eq_zero.1 this).resolve_right ht
    have hc0 : c = 0 := by
      have : c * (a + d + 1) = 0 := by linear_combination R3
      exact (mul_eq_zero.1 this).resolve_right ht
    have h2a : 2 * a + 1 = 0 := by rw [← hc, hc0]
    have h3' : (3 : K) = 0 := by
      subst hb0
      linear_combination 4 * R1a - (2 * a + 1) * h2a
    exact h3 h3'
  have hd : d = -1 - a := by linear_combination ht
  have hb : b = -(2 * a + 1) := by rw [hb', hd]; ring
  have key : 3 * (a * (a + 1)) = 0 := by
    rw [hb, hc] at R1a
    linear_combination -R1a
  rcases mul_eq_zero.1 ((mul_eq_zero.1 key).resolve_left h3) with h0 | h1
  · left
    refine LinearEquiv.ext fun ⟨x, y⟩ => ?_
    rw [hxy]
    have ha0 : a = 0 := h0
    subst ha0
    refine Prod.ext ?_ ?_ <;> simp [rotLE, hd, hb, hc] <;> ring
  · right
    refine LinearEquiv.ext fun ⟨x, y⟩ => ?_
    rw [hxy]
    have ha1 : a = -1 := by linear_combination h1
    subst ha1
    show _ = (rotLE K).symm (x, y)
    refine Prod.ext ?_ ?_ <;> simp [rotLE, hd, hb, hc] <;> ring

theorem conj_rotLE_eq_or_eq_inv (h3 : (3 : K) ≠ 0) {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) :
    g * rotLE K * g⁻¹ = rotLE K ∨ g * rotLE K * g⁻¹ = (rotLE K)⁻¹ := by
  refine eq_rotLE_or_eq_inv_of_isometry h3 (σ := g * rotLE K * g⁻¹)
    (mul_mem (mul_mem hg rotLE_mem_orthogonalGroup) (inv_mem hg)) fun p => ?_
  have h := rotLE_sq_add (g⁻¹ p)
  have h2 := congrArg g h
  rw [map_zero, map_add, map_add, LinearEquiv.apply_inv_apply'] at h2
  simpa [LinearEquiv.mul_apply] using h2

theorem commute_rotLE_of_odd_orderOf (h3 : (3 : K) ≠ 0) {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) (hodd : Odd (orderOf g)) :
    Commute g (rotLE K) := by
  rcases conj_rotLE_eq_or_eq_inv h3 hg with h | h
  · exact (commute_iff_eq _ _).2 (by rw [mul_inv_eq_iff_eq_mul] at h; exact h)
  · obtain ⟨k, hk⟩ := hodd
    have h2 : Commute (g ^ 2) (rotLE K) := by
      rw [commute_iff_eq]
      have h' : g * rotLE K = (rotLE K)⁻¹ * g := by
        rw [mul_inv_eq_iff_eq_mul] at h; exact h
      have h'' : g * (rotLE K)⁻¹ = rotLE K * g := by
        have h0 := congrArg (fun x => x⁻¹) h
        simp only [mul_inv_rev, inv_inv] at h0
        rw [← mul_inv_eq_iff_eq_mul]
        simpa [mul_assoc] using h0
      calc g ^ 2 * rotLE K = g * (g * rotLE K) := by rw [pow_two, mul_assoc]
        _ = g * ((rotLE K)⁻¹ * g) := by rw [h']
        _ = (g * (rotLE K)⁻¹) * g := by rw [mul_assoc]
        _ = (rotLE K * g) * g := by rw [h'']
        _ = rotLE K * g ^ 2 := by rw [mul_assoc, pow_two]
    have hgpow : g = (g ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      have := pow_orderOf_eq_one g
      rw [hk] at this
      calc g = g ^ (2 * k + 1) * g := by rw [this, one_mul]
        _ = g ^ (2 * (k + 1)) := by rw [← pow_succ, show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
    rw [hgpow]
    exact h2.pow_left (k + 1)

theorem orderOf_wExtend (g : (K × K) ≃ₗ[K] (K × K)) : orderOf (wExtend K g) = orderOf g :=
  orderOf_injective (wExtend K) wExtend_injective g

theorem orderOf_planeExtend (i : Fin 3) (g : (K × K) ≃ₗ[K] (K × K)) :
    orderOf (planeExtend K i g) = orderOf g :=
  orderOf_injective (planeExtend K i) (planeExtend_injective i) g

theorem wExtend_mem_modelOmega_of_odd [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (wForm b c)) (hodd : Odd (orderOf g)) :
    wExtend K g ∈ modelOmega b c :=
  mem_modelOmega_of_odd h3 hbc (wExtend_mem_modelO hg) (by rwa [orderOf_wExtend])

theorem planeExtend_mem_modelOmega_of_odd [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin 3) {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) (hodd : Odd (orderOf g)) :
    planeExtend K i g ∈ modelOmega b c :=
  mem_modelOmega_of_odd h3 hbc (planeExtend_mem_modelO i hg) (by rwa [orderOf_planeExtend])

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
