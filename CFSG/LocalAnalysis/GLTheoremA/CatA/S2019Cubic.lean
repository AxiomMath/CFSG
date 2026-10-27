module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Quadratic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial CFSG.HardMathSupport.Dickson.I271

section Linear

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {q : ℕ} [hq : Fact q.Prime] [CharP F q]

theorem commute_of_sub_one_pow_of_normalizes {k : ℕ} (hk : k + 2 ≤ q)
    {x : LinearMap.GeneralLinearGroup F V} (hxq : x ^ q = 1)
    (hxk : ((x : V →ₗ[F] V) - 1) ^ k = 0)
    {Tt : Subgroup (LinearMap.GeneralLinearGroup F V)} (hTq : ∀ g ∈ Tt, ¬ q ∣ orderOf g)
    (hnorm : ∀ g ∈ Tt, x * g * x⁻¹ ∈ Tt) : ∀ g ∈ Tt, g * x = x * g := by
  classical
  by_cases hx1 : x = 1
  · intro g _
    rw [hx1, mul_one, one_mul]
  haveI := finite_generalLinearGroup (F := F) (V := V)
  have hxo : orderOf x = q := orderOf_eq_prime hxq hx1
  have hle : Subgroup.zpowers x ≤
      Subgroup.normalizer (Tt : Set (LinearMap.GeneralLinearGroup F V)) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_pow_eq_one hq.out.pos hxq hnorm
  set G : Subgroup (LinearMap.GeneralLinearGroup F V) := Subgroup.zpowers x ⊔ Tt with hG
  set NG : Subgroup ↥G := Tt.subgroupOf G with hNG
  haveI : NG.Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
  have hxG : x ∈ G := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hTG : Tt ≤ G := le_sup_right
  have hidx : NG.index ∣ q := by
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient (Subgroup.zpowers x) Tt hle
    have h1 : Nat.card (↥G ⧸ NG) =
        Nat.card (↥(Subgroup.zpowers x) ⧸ Tt.subgroupOf (Subgroup.zpowers x)) :=
      (Nat.card_congr e.toEquiv).symm
    rw [Subgroup.index_eq_card, h1]
    have h2 := Subgroup.card_quotient_dvd_card (Tt.subgroupOf (Subgroup.zpowers x))
    rwa [Nat.card_zpowers, hxo] at h2
  have hNGcop : ¬ q ∣ Nat.card NG := by
    intro hdvd
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv] at hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Tt) q hdvd
    exact hTq (g : LinearMap.GeneralLinearGroup F V) g.2 (by rw [Subgroup.orderOf_coe, hg])
  let xG : ↥G := ⟨x, hxG⟩
  have hxGp : xG ^ q = 1 := Subtype.ext (by simpa using hxq)
  have hxGo : orderOf xG = q := by
    rw [← Subgroup.orderOf_coe xG]
    exact hxo
  rcases piCore_eq_bot_or_commute hNGcop hidx hxGp with hO | hcomm
  · exfalso
    have hPS : CFSG.HallHigman.IsPSolvable q ↥G := isPSolvable_of_normal_index_dvd hNGcop hidx
    obtain ⟨r, hr1, -, hmin, hlt, -, -⟩ :=
      CFSG.GroupTheory.HallHigmanB.hall_higman_theorem_B_minimal_polynomial G hPS hO xG
        (n := 1) le_rfl (by rw [hxGo, pow_one])
    have hxGv : ((xG : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) = (x : V →ₗ[F] V) := rfl
    rw [hxGv] at hmin
    have hdvd : (X - 1 : F[X]) ^ r ∣ (X - 1) ^ k := by
      rw [← hmin]
      apply minpoly.dvd
      simpa using hxk
    have hrk : r ≤ k := by
      have hX : (X - 1 : F[X]) = X - C 1 := by rw [map_one]
      have h := natDegree_le_of_dvd hdvd (pow_ne_zero _ (by rw [hX]; exact X_sub_C_ne_zero 1))
      rwa [hX, natDegree_pow, natDegree_pow, natDegree_X_sub_C, mul_one, mul_one] at h
    obtain ⟨n₀, -, -, hn₀, hn₀1, -, -, -, -, hbound⟩ := hlt (by rw [pow_one]; omega)
    obtain rfl : n₀ = 1 := le_antisymm hn₀1 hn₀
    rw [Nat.sub_self, pow_zero, one_mul, pow_one] at hbound
    omega
  · intro g hg
    have hgN : (⟨g, hTG hg⟩ : ↥G) ∈ NG := Subgroup.mem_subgroupOf.2 hg
    exact congrArg (fun z : ↥G => (z : LinearMap.GeneralLinearGroup F V)) (hcomm _ hgN)

end Linear

section Group

theorem commutator_eq_bot_of_noncentral_mem_centralizer {S : Type*} [Group S] {J T : Subgroup S}
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJT : J ≤ Subgroup.normalizer (T : Set S)) {s : S}
    (hsJ : s ∈ J) (hsZ : ∃ j ∈ J, j * s ≠ s * j)
    (hsC : s ∈ Subgroup.centralizer (T : Set S)) : ⁅T, J⁆ = ⊥ := by
  set N : Subgroup ↥J := (Subgroup.centralizer (T : Set S)).subgroupOf J with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn j => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
    intro t ht
    have hj : (j : S) ∈ Subgroup.normalizer (T : Set S) := hJT j.2
    have ht' : (j : S)⁻¹ * t * (j : S) ∈ T := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hj) t).1 ht
      simpa [mul_assoc] using this
    have h1 := hn _ ht'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc t * ((j : S) * n * (j : S)⁻¹)
        = (j : S) * (((j : S)⁻¹ * t * (j : S)) * n) * (j : S)⁻¹ := by group
      _ = (j : S) * (n * ((j : S)⁻¹ * t * (j : S))) * (j : S)⁻¹ := by rw [h1]
      _ = (j : S) * n * (j : S)⁻¹ * t := by group
  have hNtop : N = ⊤ := by
    by_contra hne
    have hZ := CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hJq hNn hne
    have hsN : (⟨s, hsJ⟩ : ↥J) ∈ N := Subgroup.mem_subgroupOf.2 hsC
    obtain ⟨j, hj, hjs⟩ := hsZ
    apply hjs
    have := Subgroup.mem_center_iff.1 (hZ hsN) ⟨j, hj⟩
    exact congrArg Subtype.val this
  have hJC : J ≤ Subgroup.centralizer (T : Set S) := fun j hj => by
    have : (⟨j, hj⟩ : ↥J) ∈ N := hNtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.1 hJC

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {q : ℕ} [hq : Fact q.Prime] [CharP F q]

theorem commutator_eq_bot_of_sub_one_pow_lift {k : ℕ} (hk : k + 2 ≤ q) {S K : Type*} [Group S]
    [Group K] {J T : Subgroup S} (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJT : J ≤ Subgroup.normalizer (T : Set S)) (hT : ∀ t ∈ T, ¬ q ∣ orderOf t)
    (π : K →* S) (hπ : Function.Surjective π) (hker : ∀ w ∈ π.ker, ¬ q ∣ orderOf w)
    (ρ : K →* LinearMap.GeneralLinearGroup F V) (hρ : Function.Injective ρ) {u : K}
    (huJ : π u ∈ J) (huZ : ∃ j ∈ J, j * π u ≠ π u * j) (huq : u ^ q = 1)
    (huk : (((ρ u : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) - 1) ^ k = 0) :
    ⁅T, J⁆ = ⊥ := by
  classical
  set Tt : Subgroup (LinearMap.GeneralLinearGroup F V) := (T.comap π).map ρ with hTt
  have hTtq : ∀ g ∈ Tt, ¬ q ∣ orderOf g := by
    rintro _ ⟨w, hw, rfl⟩
    rw [orderOf_injective ρ hρ w]
    exact not_dvd_orderOf_of_mem_comap hT π hker hw
  have huN : π u ∈ Subgroup.normalizer (T : Set S) := hJT huJ
  have hnorm : ∀ g ∈ Tt, ρ u * g * (ρ u)⁻¹ ∈ Tt := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨u * w * u⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change π (u * w * u⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 huN (π w)).1 hw
  have hcomm := commute_of_sub_one_pow_of_normalizes hk
    (by rw [← map_pow, huq, map_one]) huk hTtq hnorm
  have huC : π u ∈ Subgroup.centralizer (T : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨w, rfl⟩ := hπ t
    have h1 := hcomm (ρ w) ⟨w, ht, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    rw [← map_mul, ← map_mul, hρ h1]
  exact commutator_eq_bot_of_noncentral_mem_centralizer hJq hJT huJ huZ huC

end Group

end CFSG.LocalAnalysis.GLTheoremA.S2019
