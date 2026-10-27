module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisBase

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5L2

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem eq_one_or_neg_one_of_mul_self {b : Fˣ} (h : b * b = 1) : b = 1 ∨ b = -1 := by
  have h1 : (b : F) * b = 1 := by rw [← Units.val_mul, h, Units.val_one]
  rcases mul_self_eq_one_iff.mp h1 with h2 | h2
  · exact Or.inl (Units.ext h2)
  · exact Or.inr (Units.ext (by rw [h2, Units.val_neg, Units.val_one]))

omit [Finite F] in
theorem fu_of_mul_self (σ : F ≃+* F) {b : Fˣ} (h : b * b = 1) : fu F σ b = b := by
  rcases eq_one_or_neg_one_of_mul_self h with rfl | rfl
  · exact map_one _
  · exact fu_neg_one σ

omit [Finite F] in
theorem twist_of_mul_self (ε : Bool) {b : Fˣ} (h : b * b = 1) : twist F ε b = b := by
  cases ε
  · rfl
  · exact inv_eq_of_mul_eq_one_right h

variable (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (hn : 3 ≤ twoVal F)
include hodd hsq hn

theorem mul_self_of_centralizes_stdT (x : PGammaL2 F)
    (hx : ∀ g ∈ (stdT F).map (incl F), x * g = g * x) (hσ : x.right * x.right = 1) :
    x * x = 1 := by
  obtain ⟨b, ε, hxb⟩ := exists_nm_of_normalizes_stdT hodd hsq hn x (fun g hg => by
    rw [hx g hg, mul_inv_cancel_right]
    exact hg)
  have hsw : nm F 1 true 1 ∈ (stdT F).map (incl F) :=
    (mem_map_stdT_iff hsq _).mpr ⟨1, one_mem _, true, rfl⟩
  have h1 := hx _ hsw
  rw [hxb, nm_mul, nm_mul, nm_eq_nm_iff] at h1
  have hb : b * b = 1 := by
    have h2 := h1.1
    simp only [map_one, twist_one, mul_one, one_mul, fu_one, twist_true] at h2
    rw [mul_eq_one_iff_eq_inv]
    exact h2
  rw [hxb, nm_mul, fu_of_mul_self _ hb, twist_of_mul_self _ hb, hb, Bool.xor_self, hσ, nm_one]

theorem commute_of_sq_mem_stdT (w : PGammaL2 F)
    (hw : ∀ g ∈ (stdT F).map (incl F), w * g * w⁻¹ ∈ (stdT F).map (incl F))
    (hc : w * w ∈ (stdT F).map (incl F)) (hc2 : w * w * (w * w) = 1) :
    ∀ g ∈ (stdT F).map (incl F), w * w * g = g * (w * w) := by
  obtain ⟨b, ε, hwb⟩ := exists_nm_of_normalizes_stdT hodd hsq hn w hw
  set σ := w.right with hσ
  obtain ⟨y, -, ε', hy⟩ := (mem_map_stdT_iff hsq _).mp hc
  have hww : w * w = nm F (b * twist F ε (fu F σ b)) false (σ * σ) := by
    rw [hwb, nm_mul, Bool.xor_self]
  rw [hww, nm_eq_nm_iff] at hy
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have hw2 : w * w = nm F y false 1 := by rw [hww, hy1, hy3]
  have hyy : y * y = 1 := by
    rw [hw2, nm_mul, ← nm_one, nm_eq_nm_iff] at hc2
    simpa [fu_one] using hc2.1
  intro g hg
  obtain ⟨y', -, ε'', rfl⟩ := (mem_map_stdT_iff hsq _).mp hg
  rw [hw2, nm_mul, nm_mul]
  simp only [fu_one, twist_false, twist_of_mul_self _ hyy]
  rw [mul_comm y y']
  simp

omit hn in
include hn in
theorem exists_field_central {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    ∃ y : PGammaL2 F, y.right = σ ∧ y * y = 1 ∧
      ∀ g ∈ (stdT F).map (incl F), y * g = g * y := by
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hc₀ := orderOf_stdGen_sq hodd
  rcases fix_or_inv_of_order_two hp hp2 hF σ (by rw [pow_one]; exact hσ) (stdGen F ^ 2) hc₀
    (by omega) with h | h
  · refine ⟨nm F 1 false σ, rfl, ?_, ?_⟩
    · rw [nm_mul, hσσ, map_one, twist_false, mul_one, Bool.xor_self, nm_one]
    · intro g hg
      obtain ⟨y', hy', ε', rfl⟩ := (mem_map_stdT_iff hsq _).mp hg
      obtain ⟨i, rfl⟩ := hy'
      rw [nm_mul, nm_mul, map_zpow, h, twist_false, one_mul, fu_one, twist_one, mul_one,
        mul_one, one_mul, Bool.false_xor, Bool.xor_false]
  · refine ⟨nm F 1 true σ, rfl, ?_, ?_⟩
    · rw [nm_mul, hσσ, map_one, twist_one, mul_one, Bool.xor_self, nm_one]
    · intro g hg
      obtain ⟨y', hy', ε', rfl⟩ := (mem_map_stdT_iff hsq _).mp hg
      obtain ⟨i, rfl⟩ := hy'
      rw [nm_mul, nm_mul, map_zpow, h, twist_true, inv_zpow, inv_inv, one_mul, fu_one,
        twist_one, mul_one, mul_one, one_mul, Bool.true_xor, Bool.xor_true]

omit hodd hsq hn

theorem model_hyps_of_even {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hfe : Even f) :
    IsSquare (-1 : F) ∧ Nat.card F % 4 = 1 ∧ 3 ≤ twoVal F := by
  have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hfe
  refine ⟨?_, hq4, ?_⟩
  · have : Fintype F := Fintype.ofFinite F
    classical
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  · obtain ⟨k, rfl⟩ := hfe
    have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
    have h8 : 8 ∣ p ^ (k + k) - 1 := by
      rw [← two_mul, pow_mul']
      obtain ⟨t, ht⟩ := hodd
      rw [ht]
      have h1 : (2 * t + 1) ^ 2 - 1 = 4 * (t * (t + 1)) := by
        rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
        ring
      rw [h1]
      obtain ⟨u, hu⟩ := Nat.even_mul_succ_self t
      rw [hu]
      exact ⟨u, by ring⟩
    rw [twoVal, hF]
    have h0 : p ^ (k + k) - 1 ≠ 0 := by
      have : 1 < p ^ (k + k) := Nat.one_lt_pow (by omega) hp.one_lt
      omega
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h0).mp (by simpa using h8)

end CFSG.ComponentClassification.FooteLit.Aut5L2
