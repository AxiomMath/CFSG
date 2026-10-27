module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.SP.Local

private theorem card_centralizer_mul_card_isConj {G : Type} [Group G] [Finite G] (x : G) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) * Nat.card {a : G // IsConj x a} =
      Nat.card G := by
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set G))
  rw [Subgroup.index_centralizer_eq_ncard, ← Nat.card_coe_set_eq] at h
  exact h

private theorem card_conj_comm_eq {G : Type} [Group G] (u v a : G) (ha : IsConj u a) :
    Nat.card {b : G // IsConj v b ∧ a * b = b * a} =
      Nat.card {b : G // IsConj v b ∧ u * b = b * u} := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp ha
  refine Nat.card_congr (Equiv.subtypeEquiv ((MulAut.conj c⁻¹).toEquiv) fun b => ?_)
  have hb : (MulAut.conj c⁻¹).toEquiv b = c⁻¹ * b * c := by
    simp
  rw [hb]
  have hconj : IsConj v (c⁻¹ * b * c) ↔ IsConj v b := by
    have h1 : IsConj b (c⁻¹ * b * c) := isConj_iff.mpr ⟨c⁻¹, by simp⟩
    exact ⟨fun h => h.trans h1.symm, fun h => h.trans h1⟩
  have hcomm : c * u * c⁻¹ * b = b * (c * u * c⁻¹) ↔ u * (c⁻¹ * b * c) = c⁻¹ * b * c * u := by
    constructor
    · intro h
      calc u * (c⁻¹ * b * c) = c⁻¹ * (c * u * c⁻¹ * b) * c := by group
        _ = c⁻¹ * (b * (c * u * c⁻¹)) * c := by rw [h]
        _ = c⁻¹ * b * c * u := by group
    · intro h
      calc c * u * c⁻¹ * b = c * (u * (c⁻¹ * b * c)) * c⁻¹ := by group
        _ = c * (c⁻¹ * b * c * u) * c⁻¹ := by rw [h]
        _ = b * (c * u * c⁻¹) := by group
  rw [hconj, hcomm]

private theorem card_pairs_eq {G : Type} [Group G] [Finite G] (u v : G) :
    Nat.card {p : G × G // IsConj u p.1 ∧ IsConj v p.2 ∧ p.1 * p.2 = p.2 * p.1} =
      Nat.card {a : G // IsConj u a} * Nat.card {b : G // IsConj v b ∧ u * b = b * u} := by
  have : Fintype {a : G // IsConj u a} := Fintype.ofFinite _
  let e : {p : G × G // IsConj u p.1 ∧ IsConj v p.2 ∧ p.1 * p.2 = p.2 * p.1} ≃
      Σ a : {a : G // IsConj u a}, {b : G // IsConj v b ∧ (a : G) * b = b * a} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1, p.2.2.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2, s.2.2.1, s.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfib : ∀ a : {a : G // IsConj u a},
      Nat.card {b : G // IsConj v b ∧ (a : G) * b = b * a} =
        Nat.card {b : G // IsConj v b ∧ u * b = b * u} :=
    fun a => card_conj_comm_eq u v a a.2
  rw [Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl (fun a _ => hfib a),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]

private theorem cancel_card {g cx cy nX nY m₁ m₂ : ℕ} (hg : 0 < g) (hx : cx * nX = g)
    (hy : cy * nY = g) (h : nX * m₁ = nY * m₂) : cy * m₁ = cx * m₂ := by
  refine Nat.eq_of_mul_eq_mul_left hg ?_
  calc g * (cy * m₁) = (cx * nX) * cy * m₁ := by rw [hx]; ring
    _ = cx * cy * (nX * m₁) := by ring
    _ = cx * cy * (nY * m₂) := by rw [h]
    _ = cx * (cy * nY) * m₂ := by ring
    _ = g * (cx * m₂) := by rw [hy]; ring

theorem card_conj_inter_comm {G : Type} [Group G] [Finite G] (x y : G) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) *
        Nat.card {b : G // IsConj y b ∧ b ∈ Subgroup.centralizer ({x} : Set G)} =
      Nat.card (Subgroup.centralizer ({x} : Set G)) *
        Nat.card {a : G // IsConj x a ∧ a ∈ Subgroup.centralizer ({y} : Set G)} := by
  have hswap : Nat.card {p : G × G // IsConj x p.1 ∧ IsConj y p.2 ∧ p.1 * p.2 = p.2 * p.1} =
      Nat.card {p : G × G // IsConj y p.1 ∧ IsConj x p.2 ∧ p.1 * p.2 = p.2 * p.1} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.prodComm G G) fun p => by
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h2, h1, h3.symm⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h2, h1, h3.symm⟩)
  have h₁ : Nat.card {b : G // IsConj y b ∧ b ∈ Subgroup.centralizer ({x} : Set G)} =
      Nat.card {b : G // IsConj y b ∧ x * b = b * x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun b => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact and_congr_right fun _ => eq_comm)
  have h₂ : Nat.card {a : G // IsConj x a ∧ a ∈ Subgroup.centralizer ({y} : Set G)} =
      Nat.card {a : G // IsConj x a ∧ y * a = a * y} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact and_congr_right fun _ => eq_comm)
  rw [h₁, h₂]
  refine cancel_card Nat.card_pos (card_centralizer_mul_card_isConj x)
    (card_centralizer_mul_card_isConj y) ?_
  rw [← card_pairs_eq x y, hswap, card_pairs_eq y x]

private theorem order_identity_int (q d s δ e I ι ι' O P f N₁ N₂ : ℤ)
    (E1 : d + s = 2 * q) (E2 : d * s + 1 = q ^ 2) (E3 : 2 * δ = d)
    (E4 : 2 * I = q * (d * s)) (E5 : 2 * ι = q * s) (E6 : 2 * ι' = q * d)
    (hN₁ : N₁ + e = δ) (hN₂ : N₂ + 2 * e = δ)
    (hO : O + ι * N₁ = I) (hP : P + ι * (δ * N₁) = ι * ι) :
    2 * (4 * f * I ^ 2 * (δ * (N₂ * ι + δ * ι') + P) + 4 * δ * I * f * (I * O)) =
      q ^ 4 * (d * s) * (d * s * (q ^ 2 + 1)) * f := by
  have hO' : O = I - ι * N₁ := by linarith
  have hP' : P = ι * ι - ι * (δ * N₁) := by linarith
  have hN₁' : N₁ = δ - e := by linarith
  have hN₂' : N₂ = δ - 2 * e := by linarith
  have hB : δ * (N₂ * ι + δ * ι') + P + δ * O = δ ^ 2 * (ι' - ι) + ι ^ 2 + δ * I := by
    rw [hO', hP', hN₂', hN₁']
    ring
  have hB8 : 8 * (δ ^ 2 * (ι' - ι) + ι ^ 2 + δ * I) = 4 * q ^ 2 * (q ^ 2 + 1) := by
    linear_combination (q * d ^ 2 + 2 * q ^ 2 * (d + s + 2 * q)) * E1 +
      (q * (d - s) * (2 * δ + d) + 2 * q * d * s) * E3 - 4 * q ^ 2 * E2 + 4 * δ ^ 2 * E6 +
      (2 * (2 * ι + q * s) - 4 * δ ^ 2) * E5 + 4 * δ * E4
  have hlhs : 2 * (4 * f * I ^ 2 * (δ * (N₂ * ι + δ * ι') + P) + 4 * δ * I * f * (I * O)) =
      f * I ^ 2 * (8 * (δ * (N₂ * ι + δ * ι') + P + δ * O)) := by ring
  rw [hlhs, hB, hB8]
  have hI2 : I ^ 2 * 4 = (q * (d * s)) ^ 2 := by rw [← E4]; ring
  calc f * I ^ 2 * (4 * q ^ 2 * (q ^ 2 + 1)) = f * (I ^ 2 * 4) * (q ^ 2 * (q ^ 2 + 1)) := by ring
    _ = f * (q * (d * s)) ^ 2 * (q ^ 2 * (q ^ 2 + 1)) := by rw [hI2]
    _ = q ^ 4 * (d * s) * (d * s * (q ^ 2 + 1)) * f := by ring

theorem order_identity (q d s δ e I ι ι' O P f : ℕ) (hq : 5 ≤ q)
    (hds : d + s = 2 * q) (hds2 : d * s + 1 = q ^ 2) (hc : s = d + 2 ∨ d = s + 2)
    (hδ : 2 * δ = d) (he : 2 * e ≤ δ)
    (hI : 2 * I = q * (q ^ 2 - 1)) (hι : ι * d = I) (hι' : ι' * s = I)
    (hO : O + ι * (δ - e) = I) (hP : P + ι * (δ * (δ - e)) = ι * ι) :
    2 * (4 * f * I ^ 2 * (δ * ((δ - 2 * e) * ι + δ * ι') + P) + 4 * δ * I * f * (I * O)) =
      q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) * f := by
  have _ := hc
  have hq2 : 25 ≤ q ^ 2 := by nlinarith
  have hd : 0 < d := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    omega
  have hs : 0 < s := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    omega
  have hq21 : q ^ 2 - 1 = d * s := by omega
  have hq41 : q ^ 4 - 1 = d * s * (q ^ 2 + 1) := by
    refine Nat.sub_eq_of_eq_add ?_
    have h : (d : ℤ) * s + 1 = (q : ℤ) ^ 2 := by exact_mod_cast hds2
    have h4 : (q : ℤ) ^ 4 = d * s * (q ^ 2 + 1) + 1 := by
      linear_combination (-((q : ℤ) ^ 2 + 1)) * h
    exact_mod_cast h4
  rw [hq21] at hI
  rw [hq21, hq41]
  have hE5 : 2 * ι = q * s := by
    refine Nat.eq_of_mul_eq_mul_left hd ?_
    calc d * (2 * ι) = 2 * (ι * d) := by ring
      _ = q * (d * s) := by rw [hι]; exact hI
      _ = d * (q * s) := by ring
  have hE6 : 2 * ι' = q * d := by
    refine Nat.eq_of_mul_eq_mul_left hs ?_
    calc s * (2 * ι') = 2 * (ι' * s) := by ring
      _ = q * (d * s) := by rw [hι']; exact hI
      _ = s * (q * d) := by ring
  obtain ⟨N₁, hN₁⟩ : ∃ N₁, N₁ = δ - e := ⟨_, rfl⟩
  obtain ⟨N₂, hN₂⟩ : ∃ N₂, N₂ = δ - 2 * e := ⟨_, rfl⟩
  have hN₁' : N₁ + e = δ := by omega
  have hN₂' : N₂ + 2 * e = δ := by omega
  rw [← hN₁] at hO hP
  rw [← hN₂]
  have key := order_identity_int q d s δ e I ι ι' O P f N₁ N₂ (by exact_mod_cast hds)
    (by exact_mod_cast hds2) (by exact_mod_cast hδ) (by exact_mod_cast hI)
    (by exact_mod_cast hE5) (by exact_mod_cast hE6) (by exact_mod_cast hN₁')
    (by exact_mod_cast hN₂') (by exact_mod_cast hO) (by exact_mod_cast hP)
  exact_mod_cast key

private theorem not_dvd_pow_pow_sub_one {p k m : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ¬ p ∣ (p ^ k) ^ m - 1 := by
  intro h
  have hdvd : p ∣ (p ^ k) ^ m :=
    dvd_pow (dvd_pow_self p (by omega)) (by omega)
  have hpos : 0 < (p ^ k) ^ m := pow_pos (pow_pos hp.pos k) m
  have hsum : (p ^ k) ^ m = ((p ^ k) ^ m - 1) + 1 := by omega
  rw [hsum] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp hdvd))

theorem sylow_card_of_card {G : Type} [Group G] [Finite G] (p k f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 1 ≤ k) (hf : 0 < f)
    (hcard : 2 * Nat.card G = (p ^ k) ^ 4 * ((p ^ k) ^ 2 - 1) * ((p ^ k) ^ 4 - 1) * f)
    (T : Sylow p G) :
    Nat.card ↥T = (p ^ k) ^ 4 * p ^ f.factorization p := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hpk : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  have hA : (p ^ k) ^ 4 ≠ 0 := pow_ne_zero 4 (by omega)
  have hB : (p ^ k) ^ 2 - 1 ≠ 0 := by
    have : 1 < (p ^ k) ^ 2 := Nat.one_lt_pow (by omega) hpk
    omega
  have hC : (p ^ k) ^ 4 - 1 ≠ 0 := by
    have : 1 < (p ^ k) ^ 4 := Nat.one_lt_pow (by omega) hpk
    omega
  have hf0 : f ≠ 0 := by omega
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hp2' : ¬ p ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hp2 h1
  have h2 : (2 * Nat.card G).factorization p = (Nat.card G).factorization p := by
    rw [Nat.factorization_mul two_ne_zero hG, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hp2', zero_add]
  have hpow : ((p ^ k) ^ 4).factorization p = 4 * k := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.factorization_pow, Finsupp.smul_apply,
      hp.factorization_self, smul_eq_mul, smul_eq_mul]
    ring
  have hB0 : ((p ^ k) ^ 2 - 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_pow_pow_sub_one hp hk (by norm_num))
  have hC0 : ((p ^ k) ^ 4 - 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_pow_pow_sub_one hp hk (by norm_num))
  have hR : (2 * Nat.card G).factorization p = 4 * k + f.factorization p := by
    rw [hcard, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hA hB) hC) hf0, Finsupp.add_apply,
      Nat.factorization_mul (mul_ne_zero hA hB) hC, Finsupp.add_apply,
      Nat.factorization_mul hA hB, Finsupp.add_apply, hpow, hB0, hC0]
    ring
  have hT : Nat.card ↥T = p ^ (Nat.card G).factorization p := Sylow.card_eq_multiplicity T
  rw [hT, ← h2, hR, pow_add, pow_mul']

end CFSG.GH74.GLS.SP.Local
