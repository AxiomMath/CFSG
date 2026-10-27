module

public import CFSG.LargeExtraspecial.Asc611ILift
public import CFSG.LargeExtraspecial.Asc611ILemZ
public import CFSG.LargeExtraspecial.Asc611IBasic

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem pow_smul_periodic {g : SUid frob m} {a b : Fin m → K} {μ : K} (h1 : g • a = μ • b)
    (h2 : g • (μ • b) = μ • b + a) (n : ℕ) :
    g ^ n • a = if n % 3 = 0 then a else if n % 3 = 1 then μ • b else μ • b + a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih]
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · rw [ite_eq_left h, h1, ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_left h, h2, ite_eq_right (by omega),
        ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), smul_add, h2, h1,
        ite_eq_left (by omega),
        add_assoc, add_comm a, ← add_assoc, vec_add_self, zero_add]

theorem two_pow_mod_three (r : ℕ) : 2 ^ r % 3 = 1 ∨ 2 ^ r % 3 = 2 := by
  induction r with
  | zero => left; rfl
  | succ r ih => rw [pow_succ]; omega

theorem herm_invN_eq_zero_of_mem (hm : 3 ≤ m) {e : SUid frob m} (he : e * e = 1)
    {U : Subgroup (PG m)} (hU : IsPGroup 2 U)
    (hUN : ∀ c ∈ centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m)), ∀ u ∈ U,
      c * u * c⁻¹ ∈ U)
    {k : SUid frob m} (hk : (QuotientGroup.mk k : PG m) ∈ U) (hke : k * e = e * k)
    {y : Fin m → K} (hy : herm frob y y = 0) (hyN : herm frob y (invN e y) = 0) :
    herm frob y (invN e (k • y)) = 0 := by
  by_contra hμ
  set μ := herm frob y (invN e (k • y)) with hμdef
  have hg : (QuotientGroup.mk (k * cv e y * k⁻¹ * (cv e y)⁻¹) : PG m) ∈ U :=
    mk_comm_mem hUN hk (cv_comm he hy hyN)
  obtain ⟨r, c, hc⟩ := exists_pow_scalar hm hU hg
  have hky : herm frob (k • y) (k • y) = 0 := by rw [herm_smul_smul, hy]
  have hkyN : herm frob (k • y) (invN e (k • y)) = 0 := by
    rw [herm_invN_smul_smul hke, hyN]
  have hey : herm frob (e • y) (e • y) = 0 := by rw [herm_smul_smul, hy]
  have hgeq : k * cv e y * k⁻¹ * (cv e y)⁻¹ = cv e (k • y) * cv e y := by
    rw [cv_inv hy hyN, conj_cv hke hy hey]
  rw [hgeq] at hc
  set a := invN e (k • y) with ha
  set b := invN e y with hb
  have ha0 : invN e a = 0 := invN_invN he _
  have hb0 : invN e b = 0 := invN_invN he _
  have hkyb : herm frob (k • y) b = frob μ := herm_invN_swap he y (k • y)
  have hμμ : μ * frob μ = 1 := mul_frob_self hμ
  have hNab : ∀ s t : K, invN e (s • a + t • b) = 0 := fun s t => by
    rw [invN_add, invN_smul, invN_smul, ha0, hb0, smul_zero, smul_zero, add_zero]
  have hg1 : (cv e (k • y) * cv e y) • a = μ • b := by
    rw [mul_smul, cv_smul_ker he hy hyN ha0]
    have h0 : invN e (a + μ • b) = 0 := by
      have := hNab 1 μ; rwa [one_smul] at this
    rw [cv_smul_ker he hky hkyN h0, herm_add_right, herm_smul_right, hkyN, hkyb, hμμ,
      zero_add, one_smul, add_comm a, add_assoc, vec_add_self, add_zero]
  have hg2 : (cv e (k • y) * cv e y) • (μ • b) = μ • b + a := by
    have h0 : invN e (μ • b) = 0 := by rw [invN_smul, hb0, smul_zero]
    rw [mul_smul, cv_smul_ker he hy hyN h0, herm_smul_right, hyN, mul_zero, zero_smul,
      add_zero, cv_smul_ker he hky hkyN h0, herm_smul_right, hkyb, hμμ, one_smul]
  have hper := pow_smul_periodic hg1 hg2 (2 ^ r)
  rw [hc] at hper
  have := congrArg (herm frob (k • y)) hper
  rw [herm_smul_right, hkyN, mul_zero] at this
  rcases two_pow_mod_three r with h | h
  · rw [ite_eq_right (by omega), ite_eq_left h, herm_smul_right, hkyb, hμμ] at this
    exact zero_ne_one this
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), herm_add_right, herm_smul_right,
      hkyb, hμμ,
      hkyN, add_zero] at this
    exact zero_ne_one this

theorem isSesq_H (e : SUid frob m) : IsSesq (fun x z => herm frob x (invN e z)) where
  add_left x x' z := herm_add_left frob x x' _
  add_right x z z' := by simp only [invN_add, herm_add_right]
  smul_left c x z := herm_smul_left frob c x _
  smul_right c x z := by simp only [invN_smul, herm_smul_right]

theorem isSesq_kH (e k : SUid frob m) : IsSesq (fun x z => herm frob (k • x) (invN e z)) where
  add_left x x' z := by simp only [smul_add, herm_add_left]
  add_right x z z' := by simp only [invN_add, herm_add_right]
  smul_left c x z := by simp only [smul_comm k c x, herm_smul_left]
  smul_right c x z := by simp only [invN_smul, herm_smul_right]

theorem exists_isotropic_shift {e : SUid frob m} (he : e * e = 1) {a : Fin m → K}
    (hNa : invN e a ≠ 0) :
    ∃ z : Fin m → K, ∃ c : K, herm frob (a + c • invN e z) (a + c • invN e z) = 0 := by
  obtain ⟨z, hz⟩ := exists_herm_eq_one frob hNa
  obtain ⟨c, hc⟩ := exists_add_frob_eq
    ((frob_eq_self_iff _).1 (herm_self_fixed frob frob_frob a))
  refine ⟨z, c, ?_⟩
  have h1 : herm frob a (invN e z) = 1 := by rw [← herm_invN_left he, hz]
  have h2 : herm frob (invN e z) a = 1 := by rw [herm_conj frob frob_frob, h1, map_one]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, h1, h2,
    herm_invN_invN he, mul_zero, add_zero, mul_one]
  linear_combination hc + herm frob a a * two_eq_zero

theorem invN_smul_eq (hm : 3 ≤ m) {e : SUid frob m} (he : e * e = 1)
    {U : Subgroup (PG m)} (hU : IsPGroup 2 U)
    (hUN : ∀ c ∈ centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m)), ∀ u ∈ U,
      c * u * c⁻¹ ∈ U)
    {k : SUid frob m} (hk : (QuotientGroup.mk k : PG m) ∈ U) (hke : k * e = e * k)
    {r : ℕ} (hkr : k ^ 2 ^ r = 1) {q y : Fin m → K} (hq : herm frob q (invN e q) = 1)
    (hy : herm frob y (invN e y) = 1) (hqy : herm frob q (invN e y) = 0) (x : Fin m → K) :
    invN e (k • x) = invN e x := by
  have hHc : ∀ x z : Fin m → K, herm frob z (invN e x) = frob (herm frob x (invN e z)) :=
    fun x z => herm_invN_swap he x z
  have hS0 : ∀ a, herm frob a (invN e a) = 0 → herm frob (k • a) (invN e a) = 0 := by
    intro a ha
    by_cases hNa : invN e a = 0
    · rw [hNa, herm_zero_right]
    obtain ⟨z, c, hiso⟩ := exists_isotropic_shift he hNa
    set w := c • invN e z with hw
    have hNw : invN e w = 0 := by rw [hw, invN_smul, invN_invN he, smul_zero]
    have hH' : herm frob (a + w) (invN e (a + w)) = 0 := by
      rw [invN_add, hNw, add_zero, herm_add_left, ha, hw, herm_smul_left,
        herm_invN_invN he, mul_zero, add_zero]
    have hA := herm_invN_eq_zero_of_mem hm he hU hUN hk hke hiso hH'
    have h1 : herm frob (k • (a + w)) (invN e (a + w)) = 0 := by
      rw [herm_invN_swap he (a + w) (k • (a + w)), hA, map_zero]
    rw [invN_add, hNw, add_zero, smul_add, herm_add_left, hw, smul_comm k c,
      ← invN_smul_of_comm hke, herm_smul_left, herm_invN_invN he, mul_zero, add_zero] at h1
    exact h1
  have hZ := eq_smul_of_isotropic (isSesq_H e) hHc (isSesq_kH e k) hS0 hq hy hqy
  set ν := herm frob (k • q) (invN e q) with hν
  have hlin : ∀ x, invN e (k • x) = frob ν • invN e x := by
    intro x
    rw [← sub_eq_zero]
    refine eq_zero_of_herm frob fun z => ?_
    rw [sub_eq_add_neg, herm_add_left, herm_neg_left, herm_invN_left he, hZ x z,
      herm_smul_left, frob_frob, herm_invN_left he, add_neg_cancel]
  have hpow : ∀ n : ℕ, ∀ x, invN e (k ^ n • x) = frob ν ^ n • invN e x := by
    intro n
    induction n with
    | zero => intro x; rw [pow_zero, pow_zero, one_smul, one_smul]
    | succ n ih => intro x; rw [pow_succ', mul_smul, hlin, ih, smul_smul, ← pow_succ']
  have hq0 : invN e q ≠ 0 := by
    intro h0
    rw [h0, herm_zero_right] at hq
    exact zero_ne_one hq
  have h1 : frob ν ^ 2 ^ r = 1 := by
    have := hpow (2 ^ r) q
    rw [hkr, one_smul] at this
    have h2 : (frob ν ^ 2 ^ r - 1) • invN e q = 0 := by
      rw [sub_smul, one_smul, ← this, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hq0
  have hν0 : frob ν ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at h1
    exact zero_ne_one h1
  have h3 : frob ν ^ 3 = 1 := by
    have := frob_mul_self hν0
    rw [frob_apply] at this
    linear_combination this
  have hg := pow_gcd_eq_one.mpr ⟨h1, h3⟩
  rw [(Nat.Coprime.pow_left r (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, pow_one] at hg
  rw [hlin, hg, one_smul]

end CFSG.LargeExtraspecial.Asc611I
