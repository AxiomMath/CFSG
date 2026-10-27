module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W1

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG.GorensteinWalter CFSG.ClassicalInvolution.Q3.TL4.Z2W

section Squares

variable {F : Type} [Field F] [Finite F]

theorem isSquare_units_coe_iff (u : Fˣ) : IsSquare ((u : F)) ↔ IsSquare u := by
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [hr, mul_zero])
    refine ⟨Units.mk0 r hr0, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mk0]
    exact hr
  · rintro ⟨v, rfl⟩
    exact ⟨(v : F), by rw [Units.val_mul]⟩

theorem pD_mem_pslRange_iff (x : Fˣ) : pD x ∈ pslRange F ↔ IsSquare x := by
  rw [pD, pslRange, CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare]
  have hdet : Matrix.GeneralLinearGroup.det (glD x) = x := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, glD_val, Matrix.det_fin_two_of]
    simp
  rw [hdet]
  exact isSquare_units_coe_iff x

theorem pA_mem_pslRange_iff (x : Fˣ) : pA x ∈ pslRange F ↔ IsSquare (-x) := by
  rw [pA, pslRange, CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare]
  have hdet : Matrix.GeneralLinearGroup.det (glA x) = -x := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, glA_val, Matrix.det_fin_two_of]
    simp
  rw [hdet]
  exact isSquare_units_coe_iff (-x)

theorem isSquare_neg_one_of_four_dvd (h : 4 ∣ Nat.card Fˣ) : IsSquare (-1 : Fˣ) := by
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one_units h
  exact ⟨i, by rw [← hi, pow_two]⟩

theorem pA_mem_pslRange_iff_of_four_dvd (h : 4 ∣ Nat.card Fˣ) (x : Fˣ) :
    pA x ∈ pslRange F ↔ IsSquare x := by
  rw [pA_mem_pslRange_iff]
  obtain ⟨i, hi⟩ := isSquare_neg_one_of_four_dvd h
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨i * z, ?_⟩
    have hx : x = (-1 : Fˣ) * (-x) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_neg, Units.val_neg, Units.val_one]
      ring
    rw [hx, hz, hi, mul_mul_mul_comm]
  · rintro ⟨z, hz⟩
    refine ⟨i * z, ?_⟩
    have hneg : -x = (-1 : Fˣ) * x := by
      apply Units.ext
      rw [Units.val_mul, Units.val_neg, Units.val_neg, Units.val_one]
      ring
    rw [hneg, hz, hi, mul_mul_mul_comm]

theorem isSquare_iff_pow_eq_one (h2 : (2 : F) ≠ 0) (x : Fˣ) :
    IsSquare x ↔ x ^ (Nat.card Fˣ / 2) = 1 := by
  letI : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := by
    intro hc
    exact h2 (by
      have : CharP F 2 := (ringChar.eq_iff).mp hc
      exact CharP.cast_eq_zero F 2)
  have hodd : Odd (Fintype.card F) := by
    have hprime : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
    obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
    rw [hn]
    exact (hprime.odd_of_ne_two hF2).pow
  have hcard : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  have hexp : Fintype.card F / 2 = Nat.card Fˣ / 2 := by
    rw [hcard]
    obtain ⟨m, hm⟩ := hodd
    omega
  rw [← isSquare_units_coe_iff x, FiniteField.isSquare_iff hF2 x.ne_zero, hexp,
    ← Units.val_pow_eq_pow_val, Units.val_eq_one]

theorem exists_unit_orderOf_eq (d : ℕ) (hd : d ∣ Nat.card Fˣ) : ∃ x : Fˣ, orderOf x = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hn : Nat.card Fˣ ≠ 0 := Nat.card_pos.ne'
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hn (zero_dvd_iff.mp hd)
  have hdiv : Nat.card Fˣ / d ∣ orderOf g := by
    rw [hg]
    exact Nat.div_dvd_of_dvd hd
  refine ⟨g ^ (Nat.card Fˣ / d), ?_⟩
  rw [orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
      (Nat.pos_of_ne_zero hd0)).ne' hdiv, hg, Nat.div_div_self hd hn]

theorem unit_sq_eq_one_iff (x : Fˣ) : x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    have h5 : (x : F) * x = 1 := by
      have := congrArg Units.val hx
      simpa [sq] using this
    rcases mul_self_eq_one_iff.mp h5 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by simp [h]))
  · rintro (rfl | rfl)
    · norm_num
    · rw [pow_two]
      apply Units.ext
      simp

theorem units_neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : Fˣ) ≠ 1 :=
  neg_one_ne_one_units h2

theorem orderOf_units_neg_one (h2 : (2 : F) ≠ 0) : orderOf (-1 : Fˣ) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; apply Units.ext; simp) (units_neg_one_ne_one h2)

end Squares

section Frob

variable {F : Type} [Field F] [Finite F] {p f : ℕ}

theorem card_units_eq_of_card (hF : Nat.card F = p ^ f) : Nat.card Fˣ = p ^ f - 1 := by
  rw [Nat.card_units, hF]

theorem exists_frob_half [Fact p.Prime] (hF : Nat.card F = p ^ f) (hf : Even f) (hf0 : f ≠ 0) :
    ∃ σ₀ : F ≃+* F, σ₀ ≠ 1 ∧ σ₀ * σ₀ = 1 ∧ ∀ x : F, σ₀ x = x ^ (p ^ (f / 2)) := by
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hchar : CharP F p := charP_of_card_eq_prime_pow hcardF
  let σ₀ : F ≃+* F := RingEquiv.ofBijective (iterateFrobenius F p (f / 2))
    ⟨RingHom.injective _, Finite.surjective_of_injective (RingHom.injective _)⟩
  have hσ₀ : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2)) := fun x => iterateFrobenius_def p (f / 2) x
  obtain ⟨k, hk⟩ := hf
  have hk2 : f / 2 = k := by omega
  have hpow : p ^ (f / 2) * p ^ (f / 2) = p ^ f := by
    rw [hk2, hk, pow_add]
  refine ⟨σ₀, ?_, ?_, hσ₀⟩
  · intro h1
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
    have hfix : (g : F) ^ (p ^ (f / 2)) = (g : F) := by
      have := congrArg (fun τ : F ≃+* F => τ (g : F)) h1
      simpa [hσ₀] using this
    have hgunit : g ^ (p ^ (f / 2) - 1) = 1 := by
      have hg2 : g ^ (p ^ (f / 2)) = g := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val]
        exact hfix
      have h2 : g ^ (p ^ (f / 2) - 1) * g = 1 * g := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos), hg2,
          one_mul]
      exact mul_right_cancel h2
    have hdvd : Nat.card Fˣ ∣ p ^ (f / 2) - 1 := by
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one hgunit
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hge1 : 1 ≤ f / 2 := by omega
    have hq2 : 2 ≤ p ^ (f / 2) := by
      have h1 : p ^ 1 ≤ p ^ (f / 2) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hge1
      exact hp2.trans (by simpa using h1)
    have hpos : 0 < p ^ (f / 2) - 1 := by omega
    have hle : Nat.card Fˣ ≤ p ^ (f / 2) - 1 := Nat.le_of_dvd hpos hdvd
    have hcardu : Nat.card Fˣ = p ^ f - 1 := by rw [Nat.card_units, hF]
    have hlt : p ^ (f / 2) < p ^ f :=
      Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
    omega
  · ext x
    change σ₀ (σ₀ x) = x
    rw [hσ₀, hσ₀, ← pow_mul, hpow, ← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem ringAut_comm [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f)
    (σ τ : F ≃+* F) : σ * τ = τ * σ := by
  obtain ⟨hK, -⟩ := field_facts (Fact.out : p.Prime) hp2 hF h4
  haveI : IsCyclic (F ≃+* F) := CFSG.ClassicalInvolution.Q3.TL4.MF163.ringAut_isCyclic F hK
  exact IsCyclic.commGroup.mul_comm σ τ

theorem ringAut_sq_eq_one [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f)
    {σ₀ : F ≃+* F} (h1 : σ₀ ≠ 1) (h2 : σ₀ * σ₀ = 1) {σ : F ≃+* F} (hσ : σ * σ = 1) :
    σ = 1 ∨ σ = σ₀ := by
  obtain ⟨hK, -⟩ := field_facts (Fact.out : p.Prime) hp2 hF h4
  haveI : IsCyclic (F ≃+* F) := CFSG.ClassicalInvolution.Q3.TL4.MF163.ringAut_isCyclic F hK
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun τ : F ≃+* F => (τ : F → F)) DFunLike.coe_injective
  by_cases hσ1 : σ = 1
  · exact Or.inl hσ1
  · exact Or.inr (CFSG.ClassicalInvolution.Q3.TL4.MF163.eq_of_mul_self_eq_one hσ h2 hσ1 h1)

theorem ringAut_pow_two_pow_eq_one [Fact p.Prime] (hF : Nat.card F = p ^ f) {σ : F ≃+* F} {k : ℕ}
    (hσ : σ ^ 2 ^ k = 1) : σ ^ 2 ^ padicValNat 2 f = 1 := by
  letI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hF
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F = 1 := by rw [← Nat.card_eq_fintype_card, hF]
    omega
  have hσf : σ ^ f = 1 := ringEquiv_pow_eq_one hF σ
  have hg : σ ^ Nat.gcd (2 ^ k) f = 1 := pow_gcd_eq_one.mpr ⟨hσ, hσf⟩
  have hdvd : Nat.gcd (2 ^ k) f ∣ 2 ^ padicValNat 2 f := by
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left (2 ^ k) f)
    rw [hjeq]
    have h1 : 2 ^ j ∣ f := hjeq ▸ Nat.gcd_dvd_right (2 ^ k) f
    have h2 : j ≤ padicValNat 2 f := (padicValNat_dvd_iff_le hf0).mp h1
    exact Nat.pow_dvd_pow 2 h2
  rw [← Nat.mul_div_cancel' hdvd, pow_mul, hg, one_pow]

end Frob

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
