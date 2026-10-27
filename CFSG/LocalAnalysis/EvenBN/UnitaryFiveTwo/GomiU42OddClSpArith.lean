module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpSmallOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallCent

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.CatFC CFSG.ComponentClassification.CatFC.PSpSmall

theorem not_dvd_103680_of_three_pow_five {n : ℕ} (h5 : 3 ^ 5 ∣ n) : ¬ n ∣ 103680 := fun hn => by
  have := h5.trans hn
  norm_num at this

theorem false_of_bounds {n : ℕ} (h1 : 25920 ∣ n) (h2 : n ∣ 103680) (hlt : n < 25920 ∨ 103680 < n) :
    False := by
  have h3 := Nat.le_of_dvd (by norm_num) h2
  have h4 : 0 < n := Nat.pos_of_dvd_of_pos h2 (by norm_num)
  have h5 := Nat.le_of_dvd h4 h1
  omega

section GLOrder

variable {K : Type} [Field K] [Finite K]

theorem three_pow_dvd_card_GL {r f : ℕ} (hK : Nat.card K = 3 ^ f) :
    3 ^ (f * (r * (r - 1) / 2)) ∣ Nat.card (GL (Fin r) K) := by
  haveI := Fintype.ofFinite K
  have hq : Fintype.card K = 3 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_GL_field, hq]
  have h1 : ∀ i ∈ Finset.univ (α := Fin r), (3 ^ f) ^ (i : ℕ) ∣ (3 ^ f) ^ r - (3 ^ f) ^ (i : ℕ) :=
    fun i _ => Nat.dvd_sub (pow_dvd_pow _ i.2.le) dvd_rfl
  have h2 : 3 ^ (f * (r * (r - 1) / 2)) = ∏ i : Fin r, (3 ^ f) ^ (i : ℕ) := by
    rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) r,
      Finset.sum_range_id, ← pow_mul]
  rw [h2]
  exact Finset.prod_dvd_prod_of_dvd _ _ h1

end GLOrder

section Classes

variable {K : Type} [Field K] [Finite K]

theorem u42_not_classOne {f a b : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (h2f : a = 1 → b = 1 → 2 ≤ f) {G : Type} [Group G]
    (e : G ≃* StatedSp a K × StatedSp b K) (h1 : 25920 ∣ Nat.card G) (h2 : Nat.card G ∣ 103680) :
    False := by
  have hc : Nat.card G = Nat.card (StatedSp a K) * Nat.card (StatedSp b K) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  by_cases hbig : 5 ≤ f * (a ^ 2 + b ^ 2)
  · have h5 : 3 ^ 5 ∣ Nat.card G := by
      rw [hc]
      refine (pow_dvd_pow 3 hbig).trans ?_
      rw [mul_add, pow_add]
      exact Nat.mul_dvd_mul (three_pow_dvd_card_statedSp hK) (three_pow_dvd_card_statedSp hK)
    exact not_dvd_103680_of_three_pow_five h5 h2
  · push Not at hbig
    have ha1 : a = 1 := by
      by_contra hne
      have : 2 ≤ a := by omega
      nlinarith
    have hb1 : b = 1 := by
      by_contra hne
      have : 2 ≤ b := by omega
      nlinarith
    subst ha1 hb1
    have hf2 : f = 2 := by have := h2f rfl rfl; omega
    subst hf2
    rw [hc, card_statedSp_one, hK] at h2
    norm_num at h2

theorem u42_not_classTwo {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (hr : 2 ≤ r)
    (h2f : r = 2 → 2 ≤ f) {G : Type} [Group G] (e : G ≃* GL (Fin r) K)
    (h1 : 25920 ∣ Nat.card G) (h2 : Nat.card G ∣ 103680) : False := by
  have hc : Nat.card G = Nat.card (GL (Fin r) K) := Nat.card_congr e.toEquiv
  by_cases hbig : 5 ≤ f * (r * (r - 1) / 2)
  · have h5 : 3 ^ 5 ∣ Nat.card G := by
      rw [hc]
      exact (pow_dvd_pow 3 hbig).trans (three_pow_dvd_card_GL hK)
    exact not_dvd_103680_of_three_pow_five h5 h2
  · push Not at hbig
    haveI := Fintype.ofFinite K
    have hq : Fintype.card K = 3 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
    have hr3 : r = 2 ∨ r = 3 := by
      by_contra hne
      have h4 : 4 ≤ r := by omega
      have : 6 ≤ r * (r - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
        rw [show s + 4 - 1 = s + 3 by omega]
        nlinarith
      nlinarith
    rcases hr3 with rfl | rfl
    · have hf4 : f ≤ 4 := by norm_num at hbig; omega
      have hf2 := h2f rfl
      rw [hc, Matrix.card_GL_field, hq] at h1 h2
      interval_cases f <;> simp [Fin.prod_univ_two] at h1 h2 <;> omega
    · have hf1 : f = 1 := by norm_num at hbig; omega
      subst hf1
      rw [hc, Matrix.card_GL_field, hq] at h1 h2
      simp [Fin.prod_univ_succ] at h1 h2

theorem u42_not_classThree {E : Type} [Field E] [Finite E] {f m : ℕ} (hf : 1 ≤ f)
    (hE : Nat.card E = 3 ^ (2 * f)) (hm : 1 ≤ m) (h2f : m = 1 → 2 ≤ f) {G : Type} [Group G]
    (e : G ≃* StatedSp m E) (h1 : 25920 ∣ Nat.card G) (h2 : Nat.card G ∣ 103680) : False := by
  have hc : Nat.card G = Nat.card (StatedSp m E) := Nat.card_congr e.toEquiv
  by_cases hbig : 5 ≤ 2 * f * m ^ 2
  · have h5 : 3 ^ 5 ∣ Nat.card G := by
      rw [hc]
      exact (pow_dvd_pow 3 hbig).trans (three_pow_dvd_card_statedSp hE)
    exact not_dvd_103680_of_three_pow_five h5 h2
  · push Not at hbig
    have hm1 : m = 1 := by
      by_contra hne
      have : 2 ≤ m := by omega
      nlinarith
    subst hm1
    have hf2 : f = 2 := by have := h2f rfl; omega
    subst hf2
    rw [hc, card_statedSp_one, hE] at h2
    norm_num at h2

open CFSG.ComponentClassification.CatalogueBUnitaryIsometry in
theorem u42_not_classFour {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {f r : ℕ} (hf : 1 ≤ f)
    (hE : Nat.card E = (3 ^ f) ^ 2) (hr : 2 ≤ r) (h2f : r = 2 → 2 ≤ f)
    (hW : Module.finrank E W = r) (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsig : ∀ z, sigma z = z ^ (3 ^ f)) {G : Type} [Group G]
    (e : G ≃* isometryGroup h) (h1 : 25920 ∣ Nat.card G) (h2 : Nat.card G ∣ 103680) :
    False := by
  have hc : Nat.card G = Nat.card (isometryGroup h) := Nat.card_congr e.toEquiv
  have hcard := OmegaSmall.card_isometryGroup_unitary (ℓ := 3) (e := f) Nat.prime_three hf hE h
    hsym hnd hsig hW (by omega)
  by_cases hbig : 5 ≤ f * (r * (r - 1) / 2)
  · have h5 : 3 ^ 5 ∣ Nat.card G := by
      have hd : ((3 ^ (f * (r * (r - 1) / 2)) : ℕ) : ℤ) ∣ (Nat.card (isometryGroup h) : ℤ) := by
        rw [hcard]
        refine Dvd.dvd.mul_right ?_ _
        push_cast
        rw [← pow_mul]
      have hd' := Int.natCast_dvd_natCast.mp hd
      rw [hc]
      exact (pow_dvd_pow 3 hbig).trans hd'
    exact not_dvd_103680_of_three_pow_five h5 h2
  · push Not at hbig
    have hr3 : r = 2 ∨ r = 3 := by
      by_contra hne
      have h4 : 4 ≤ r := by omega
      have : 6 ≤ r * (r - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
        rw [show s + 4 - 1 = s + 3 by omega]
        nlinarith
      nlinarith
    rcases hr3 with rfl | rfl
    · have hf4 : f ≤ 4 := by norm_num at hbig; omega
      have hf2 := h2f rfl
      interval_cases f
      · have : (Nat.card (isometryGroup h) : ℤ) = 7200 := by
          rw [hcard]; norm_num [Finset.prod_Icc_succ_top]
        have h7 : Nat.card G = 7200 := by rw [hc]; exact_mod_cast this
        exact false_of_bounds h1 h2 (Or.inl (by omega))
      · have : (Nat.card (isometryGroup h) : ℤ) = 550368 := by
          rw [hcard]; norm_num [Finset.prod_Icc_succ_top]
        have h7 : Nat.card G = 550368 := by rw [hc]; exact_mod_cast this
        exact false_of_bounds h1 h2 (Or.inr (by omega))
      · have : (Nat.card (isometryGroup h) : ℤ) = 43571520 := by
          rw [hcard]; norm_num [Finset.prod_Icc_succ_top]
        have h7 : Nat.card G = 43571520 := by rw [hc]; exact_mod_cast this
        exact false_of_bounds h1 h2 (Or.inr (by omega))
    · have hf1 : f = 1 := by norm_num at hbig; omega
      subst hf1
      have : (Nat.card (isometryGroup h) : ℤ) = 24192 := by
        rw [hcard]; norm_num [Finset.prod_Icc_succ_top]
      have h7 : Nat.card G = 24192 := by rw [hc]; exact_mod_cast this
      exact false_of_bounds h1 h2 (Or.inl (by omega))

end Classes

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
