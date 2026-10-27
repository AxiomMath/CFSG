module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG Finset

universe u

theorem geom_sum_mod_two {t : ℤ} (ht : Odd t) (u : ℕ) :
    (∑ i ∈ range u, t ^ i) % 2 = (u : ℤ) % 2 := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [sum_range_succ, Int.add_emod, ih, Int.odd_iff.mp (ht.pow (n := u))]
    push_cast
    omega

theorem odd_geom_sum {t : ℤ} (ht : Odd t) {u : ℕ} (hu : Odd u) : Odd (∑ i ∈ range u, t ^ i) := by
  rw [Int.odd_iff, geom_sum_mod_two ht]
  exact_mod_cast Nat.odd_iff.mp hu

theorem two_pow_dvd_pow_sub_one_iff {t : ℤ} (ht : Odd t) {u : ℕ} (hu : Odd u) (k : ℕ) :
    (2 : ℤ) ^ k ∣ t ^ u - 1 ↔ (2 : ℤ) ^ k ∣ t - 1 := by
  have hcop : IsCoprime ((2 : ℤ) ^ k) (∑ i ∈ range u, t ^ i) :=
    (Int.isCoprime_two_left.mpr (odd_geom_sum ht hu)).pow_left
  rw [← geom_sum_mul t u]
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩

theorem two_pow_dvd_pow_add_one_iff {t : ℤ} (ht : Odd t) {u : ℕ} (hu : Odd u) (k : ℕ) :
    (2 : ℤ) ^ k ∣ t ^ u + 1 ↔ (2 : ℤ) ^ k ∣ t + 1 := by
  have hnt : Odd (-t) := ht.neg
  have hcop : IsCoprime ((2 : ℤ) ^ k) (∑ i ∈ range u, (-t) ^ i) :=
    (Int.isCoprime_two_left.mpr (odd_geom_sum hnt hu)).pow_left
  have hid : t ^ u + 1 = (∑ i ∈ range u, (-t) ^ i) * (t + 1) := by
    have h := geom_sum_mul (-t) u
    rw [hu.neg_pow] at h
    linear_combination h
  rw [hid]
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩

theorem two_pow_add_dvd_pow_two_pow_sub_one {t : ℤ} (ht : Odd t) {k : ℕ}
    (h : (2 : ℤ) ^ k ∣ t - 1 ∨ (2 : ℤ) ^ k ∣ t + 1) :
    ∀ e : ℕ, 1 ≤ e → (2 : ℤ) ^ (k + e) ∣ t ^ (2 ^ e) - 1 := by
  intro e he
  induction e with
  | zero => omega
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · have h2m : (2 : ℤ) ∣ t - 1 := by
        rcases ht with ⟨m, rfl⟩; exact ⟨m, by ring⟩
      have h2p : (2 : ℤ) ∣ t + 1 := by
        rcases ht with ⟨m, rfl⟩; exact ⟨m + 1, by ring⟩
      have hsq : t ^ (2 ^ (0 + 1)) - 1 = (t - 1) * (t + 1) := by ring
      rw [hsq, pow_succ]
      rcases h with h | h
      · exact mul_dvd_mul h h2p
      · rw [mul_comm (t - 1)]
        exact mul_dvd_mul h h2m
    · have ih' := ih hpos
      have hodd : Odd (t ^ 2 ^ e) := ht.pow
      have h2 : (2 : ℤ) ∣ t ^ 2 ^ e + 1 := by
        rcases hodd with ⟨m, hm⟩; exact ⟨m + 1, by rw [hm]; ring⟩
      have hfac : t ^ (2 ^ (e + 1)) - 1 = (t ^ 2 ^ e - 1) * (t ^ 2 ^ e + 1) := by ring
      rw [hfac, ← add_assoc, pow_succ]
      exact mul_dvd_mul ih' h2

variable (F : Type u) [Field F] [Finite F]

theorem frobenius_pow_apply (p : ℕ) [Fact p.Prime] [CharP F p] (j : ℕ) (x : F) :
    letI := ZMod.algebra F p
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F ^ j) x = x ^ p ^ j := by
  let := ZMod.algebra F p
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    change (x ^ p ^ j) ^ Fintype.card (ZMod p) = _
    rw [ZMod.card, ← pow_mul, ← pow_succ]

variable {F}

theorem exists_odd_pow_of_orderOf_two_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (σ : F ≃+* F) {e : ℕ} (he : 1 ≤ e) (hσ : orderOf σ = 2 ^ e) :
    ∃ t u : ℕ, Odd t ∧ Odd u ∧ Nat.card F = t ^ (2 ^ e) ∧ ∀ x : F, σ x = x ^ (t ^ u) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime_pow hcardF
  let := ZMod.algebra F p
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F
  have hfin : Module.finrank (ZMod p) F = f := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := F)
    rw [hF, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  have hbij := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (K := ZMod p) (L := F)
  rw [hfin] at hbij
  obtain ⟨⟨j, hj⟩, hjσ⟩ := hbij.2 (ringAutEquivGal F p σ)
  simp only at hjσ
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    rw [hF, pow_zero] at this
    exact lt_irrefl _ this
  have hordφ : orderOf φ = f := by
    have hφf : φ ^ f = 1 := by
      rw [← hfin, ← IsGalois.card_aut_eq_finrank]
      exact pow_card_eq_one'
    apply le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) (orderOf_dvd_of_pow_eq_one hφf))
    by_contra hlt
    push Not at hlt
    have hpos := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨f, Nat.pos_of_ne_zero hf0,
      hφf⟩)
    have h1 := hbij.1 (a₁ := ⟨orderOf φ, hlt⟩) (a₂ := ⟨0, Nat.pos_of_ne_zero hf0⟩)
      (by simp only [pow_zero]; exact pow_orderOf_eq_one φ)
    simp only [Fin.mk.injEq] at h1
    omega
  have hj0 : j ≠ 0 := by
    rintro rfl
    have hσ1 : σ = 1 := by
      apply (ringAutEquivGal F p).injective
      rw [← hjσ, map_one, pow_zero]
    rw [hσ1, orderOf_one] at hσ
    have : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  have hordσ : orderOf σ = f / Nat.gcd f j := by
    rw [← MulEquiv.orderOf_eq (ringAutEquivGal F p) σ, ← hjσ, orderOf_pow' φ hj0, hordφ]
  set d := Nat.gcd f j with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hf0)
  have hfd : f = d * 2 ^ e := by
    rw [← hσ, hordσ, Nat.mul_div_cancel' (Nat.gcd_dvd_left f j)]
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_right f j
  have hcop : Nat.Coprime (f / d) (j / d) := Nat.coprime_div_gcd_div_gcd hdpos
  have hfd' : f / d = 2 ^ e := by rw [← hσ, hordσ]
  have hjd : j / d = u := by rw [← hd] at hu; rw [hu, Nat.mul_div_cancel_left _ hdpos]
  rw [hfd', hjd] at hcop
  have huodd : Odd u := by
    rcases Nat.even_or_odd u with h | h
    · exfalso
      have h2 : 2 ∣ Nat.gcd (2 ^ e) u :=
        Nat.dvd_gcd (dvd_pow_self 2 (by omega)) (even_iff_two_dvd.mp h)
      rw [hcop] at h2
      omega
    · exact h
  refine ⟨p ^ d, u, (hp.odd_of_ne_two hp2).pow, huodd, ?_, ?_⟩
  · rw [hF, ← pow_mul, ← hfd]
  · intro x
    have hx := congrArg (fun τ : F ≃ₐ[ZMod p] F => τ x) hjσ
    change (ringAutEquivGal F p σ) x = _
    rw [← hx, frobenius_pow_apply F p j x, ← hd] at *
    rw [hu, pow_mul]

theorem two_pow_add_dvd_of_fix_or_inv {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (σ : F ≃+* F) {e : ℕ} (he : 1 ≤ e) (hσ : orderOf σ = 2 ^ e)
    (y : Fˣ) {k : ℕ} (hy : orderOf y = 2 ^ k)
    (hfix : Units.map σ.toRingHom y = y ∨ Units.map σ.toRingHom y = y⁻¹) :
    2 ^ (k + e) ∣ Nat.card F - 1 := by
  obtain ⟨t, u, ht, hu, hcard, hσx⟩ := exists_odd_pow_of_orderOf_two_pow hp hp2 hF σ he hσ
  have hσy : Units.map σ.toRingHom y = y ^ (t ^ u) := by
    ext
    simp [hσx]
  have htu : 1 ≤ t ^ u := Nat.one_le_pow _ _ (ht.pos)
  have hk : (2 : ℤ) ^ k ∣ (t : ℤ) - 1 ∨ (2 : ℤ) ^ k ∣ (t : ℤ) + 1 := by
    rcases hfix with h | h
    · left
      rw [hσy] at h
      have h1 : y ^ (t ^ u - 1) = 1 := by
        rw [pow_sub _ htu, h, pow_one, mul_inv_cancel]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hy] at h2
      have h3 : (2 : ℤ) ^ k ∣ (t : ℤ) ^ u - 1 := by
        have := Int.natCast_dvd_natCast.mpr h2
        push_cast [Nat.cast_sub htu] at this
        exact this
      exact (two_pow_dvd_pow_sub_one_iff (by exact_mod_cast ht) hu k).mp h3
    · right
      rw [hσy] at h
      have h1 : y ^ (t ^ u + 1) = 1 := by
        rw [pow_succ, h, inv_mul_cancel]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hy] at h2
      have h3 : (2 : ℤ) ^ k ∣ (t : ℤ) ^ u + 1 := by
        have := Int.natCast_dvd_natCast.mpr h2
        push_cast at this
        exact this
      exact (two_pow_dvd_pow_add_one_iff (by exact_mod_cast ht) hu k).mp h3
  have h := two_pow_add_dvd_pow_two_pow_sub_one (by exact_mod_cast ht) hk e he
  have hq1 : 1 ≤ t ^ 2 ^ e := Nat.one_le_pow _ _ ht.pos
  rw [hcard]
  have : ((2 ^ (k + e) : ℕ) : ℤ) ∣ ((t ^ 2 ^ e - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hq1]
    exact h
  exact Int.natCast_dvd_natCast.mp this

end CFSG.ComponentClassification.AutL2Facts
