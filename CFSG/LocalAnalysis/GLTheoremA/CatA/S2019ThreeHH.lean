module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Quadratic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.HardMathSupport.Dickson.I271 Polynomial

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [CharP F 3]

theorem commute_of_quadratic_three_of_abelian {x : LinearMap.GeneralLinearGroup F V}
    (hx3 : x ^ 3 = 1) (hx2 : ((x : V →ₗ[F] V) - 1) ^ 2 = 0)
    {A : Subgroup (LinearMap.GeneralLinearGroup F V)} (hA2 : IsPGroup 2 A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hnorm : ∀ a ∈ A, x * a * x⁻¹ ∈ A) :
    ∀ a ∈ A, x * a * x⁻¹ = a := by
  classical
  haveI hq : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hx1 : x = 1
  · intro a _
    rw [hx1, one_mul, inv_one, mul_one]
  haveI := finite_generalLinearGroup (F := F) (V := V)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup F V)) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_pow_eq_one (by norm_num) hx3 hnorm
  set G : Subgroup (LinearMap.GeneralLinearGroup F V) := Subgroup.zpowers x ⊔ A with hG
  set NG : Subgroup ↥G := A.subgroupOf G with hNG
  haveI : NG.Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
  have hxG : x ∈ G := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hAG : A ≤ G := le_sup_right
  have hidx : NG.index ∣ 3 := by
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient (Subgroup.zpowers x) A hle
    have h1 : Nat.card (↥G ⧸ NG) =
        Nat.card (↥(Subgroup.zpowers x) ⧸ A.subgroupOf (Subgroup.zpowers x)) :=
      (Nat.card_congr e.toEquiv).symm
    rw [Subgroup.index_eq_card, h1]
    have h2 := Subgroup.card_quotient_dvd_card (A.subgroupOf (Subgroup.zpowers x))
    rwa [Nat.card_zpowers, hxo] at h2
  have hNG2 : IsPGroup 2 NG := by
    have e : NG ≃* A := Subgroup.subgroupOfEquivOfLe hAG
    exact hA2.of_equiv e.symm
  have hNGcop : ¬ 3 ∣ Nat.card NG := by
    intro hdvd
    obtain ⟨k, hk⟩ := hNG2.exists_card_eq
    rw [hk] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hdvd)
    omega
  let xG : ↥G := ⟨x, hxG⟩
  have hxGp : xG ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hxGo : orderOf xG = 3 := by
    rw [← Subgroup.orderOf_coe xG]
    exact hxo
  rcases piCore_eq_bot_or_commute hNGcop hidx hxGp with hO | hcomm
  · exfalso
    have hPS : CFSG.HallHigman.IsPSolvable 3 ↥G := isPSolvable_of_normal_index_dvd hNGcop hidx
    obtain ⟨r, -, -, hmin, -, hexc, -⟩ :=
      CFSG.GroupTheory.HallHigmanB.hall_higman_theorem_B_minimal_polynomial G hPS hO xG
        (n := 1) le_rfl (by rw [hxGo, pow_one])
    have hr : r < 3 ^ 1 := by
      have hdvd : minpoly F ((x : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) ∣
          (X - C (1 : F)) ^ 2 := by
        apply minpoly.dvd
        rw [map_pow, map_sub, aeval_X, aeval_C, map_one]
        exact hx2
      have hmin' : minpoly F ((x : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) =
          (X - C (1 : F)) ^ r := by
        rw [map_one]
        exact hmin
      rw [hmin', pow_dvd_pow_iff (X_sub_C_ne_zero 1) (not_isUnit_X_sub_C 1)] at hdvd
      omega
    rcases hexc hr with ⟨-, hsyl, -⟩ | ⟨h2, -⟩
    ·
      obtain ⟨S⟩ : Nonempty (Sylow 2 ↥G) := inferInstance
      obtain ⟨a, haS, b, hbS, hab⟩ := hsyl S
      have hSA : ∀ s ∈ (S : Subgroup ↥G), s ∈ NG := by
        intro s hs
        obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
        have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have h1 : orderOf (QuotientGroup.mk' NG s) ∣ 2 ^ k :=
          orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk', map_one])
        have h2 : orderOf (QuotientGroup.mk' NG s) ∣ 3 :=
          (orderOf_dvd_natCard _).trans (by rw [← Subgroup.index_eq_card]; exact hidx)
        have h3 : orderOf (QuotientGroup.mk' NG s) = 1 := by
          rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h
          · exact h
          · rw [h] at h1
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
              (Nat.prime_three.dvd_of_dvd_pow h1)
            omega
        rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
        exact h3
      apply hab
      have ha := hSA a haS
      have hb := hSA b hbS
      exact Subtype.ext (hAab _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
    · omega
  · intro a ha
    have h1 := hcomm ⟨a, hAG ha⟩ (Subgroup.mem_subgroupOf.2 ha)
    have h2 : a * x = x * a := congrArg Subtype.val h1
    rw [← h2, mul_inv_cancel_right]

end CFSG.LocalAnalysis.GLTheoremA.S2019
