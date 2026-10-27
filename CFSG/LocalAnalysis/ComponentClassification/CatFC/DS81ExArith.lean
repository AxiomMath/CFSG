module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open CFSG.Open CFSG.ComponentClassification.CatLeaf

theorem two_pow_mod_of_two_pow_eleven {p : ℕ} (hp : 2 ^ 11 % p = 1) (m : ℕ) :
    2 ^ m % p = 2 ^ (m % 11) % p := by
  conv_lhs => rw [← Nat.div_add_mod m 11, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, hp, one_pow, Nat.one_mod_eq_one.mpr (by
    rintro rfl; simp at hp), one_mul, Nat.mod_mod]

theorem dvd_two_pow_sub_one_iff_mod {p : ℕ} (m : ℕ) : p ∣ 2 ^ m - 1 ↔ 1 % p = 2 ^ m % p :=
  (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).symm

theorem twentythree_dvd_two_pow_sub_one_iff (m : ℕ) : 23 ∣ 2 ^ m - 1 ↔ 11 ∣ m := by
  rw [dvd_two_pow_sub_one_iff_mod, two_pow_mod_of_two_pow_eleven (by norm_num) m,
    Nat.dvd_iff_mod_eq_zero]
  have h := Nat.mod_lt m (by norm_num : 0 < 11)
  generalize m % 11 = r at h ⊢
  interval_cases r <;> decide

theorem eightynine_dvd_two_pow_sub_one_iff (m : ℕ) : 89 ∣ 2 ^ m - 1 ↔ 11 ∣ m := by
  rw [dvd_two_pow_sub_one_iff_mod, two_pow_mod_of_two_pow_eleven (by norm_num) m,
    Nat.dvd_iff_mod_eq_zero]
  have h := Nat.mod_lt m (by norm_num : 0 < 11)
  generalize m % 11 = r at h ⊢
  interval_cases r <;> decide

theorem not_twentythree_dvd_two_pow_add_one (m : ℕ) : ¬ 23 ∣ 2 ^ m + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, two_pow_mod_of_two_pow_eleven (by norm_num) m]
  have h := Nat.mod_lt m (by norm_num : 0 < 11)
  generalize m % 11 = r at h ⊢
  interval_cases r <;> decide

theorem eleven_dvd_of_twentythree_dvd_lieOrderNumerator {t : StatedLieTag}
    (ht : t ∈ [.G2, .F4, .E6, .E7, .E8, .twistedE6, .trialityD4, .twistedB2, .twistedF4])
    {f : ℕ} (h : 23 ∣ lieOrderNumerator t 0 (2 ^ f)) : 11 ∣ f := by
  have hp : Nat.Prime 23 := by norm_num
  let Good : ℕ → Prop := fun a => 23 ∣ a → 11 ∣ f
  have good_mul : ∀ a b, Good a → Good b → Good (a * b) := fun a b ha hb hab =>
    ((Nat.Prime.dvd_mul hp).mp hab).elim ha hb
  have good_pow : ∀ k, Good ((2 ^ f) ^ k) := fun k hk => by
    have := Nat.Prime.dvd_of_dvd_pow hp (Nat.Prime.dvd_of_dvd_pow hp hk)
    norm_num at this
  have good_two_pow : Good (2 ^ f) := fun hk => by
    have := Nat.Prime.dvd_of_dvd_pow hp hk
    norm_num at this
  have good_sub : ∀ d, ¬ 11 ∣ d → Good ((2 ^ f) ^ d - 1) := fun d hd hk => by
    rw [← pow_mul, twentythree_dvd_two_pow_sub_one_iff] at hk
    exact ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 11)).mp hk).resolve_right hd
  have good_sub_one : Good (2 ^ f - 1) := by
    simpa using good_sub 1 (by norm_num)
  have good_add : ∀ d, Good ((2 ^ f) ^ d + 1) := fun d hk => by
    rw [← pow_mul] at hk
    exact absurd hk (not_twentythree_dvd_two_pow_add_one _)
  have good_d4 : Good ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) := fun hk => by
    have h1 : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ (Nat.two_pow_pos f)
    have e : ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) = (2 ^ f) ^ 12 - 1 := by
      zify [h1, Nat.one_le_pow 12 (2 ^ f) (Nat.two_pow_pos f)]
      ring
    exact good_sub 12 (by norm_num) (e ▸ Dvd.dvd.mul_left hk _)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [lieOrderNumerator] at h <;>
    · refine (?_ : Good _) h
      repeat' first
        | exact good_pow _
        | exact good_two_pow
        | exact good_sub _ (by norm_num)
        | exact good_sub_one
        | exact good_add _
        | exact good_d4
        | apply good_mul

theorem not_twentythree_dvd_lieOrderNumerator_Tits (q : ℕ) :
    ¬ 23 ∣ lieOrderNumerator .Tits 0 q := by
  simp only [lieOrderNumerator]
  decide

theorem exists_unit_orderOf_eightynine {K : Type} [Field K] [Finite K]
    (h : 89 ∣ Nat.card K - 1) : ∃ ε : Kˣ, orderOf ε = 89 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have hcard : Nat.card Kˣ = Nat.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  exact exists_prime_orderOf_dvd_card' (G := Kˣ) 89 (hcard ▸ h)

theorem exists_unit_orderOf_eightynine_of_card {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 11 ∣ f) : ∃ ε : Kˣ, orderOf ε = 89 :=
  exists_unit_orderOf_eightynine (by rw [hK]; exact (eightynine_dvd_two_pow_sub_one_iff f).2 hf)

end CFSG.ComponentClassification.CatFC.DS81.Ex
