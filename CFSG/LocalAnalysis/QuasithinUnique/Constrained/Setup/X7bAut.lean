module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Transport

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def antiProjEquiv (K : Type) [Field K] [CharP K 2] :
    antiSp K ≃* StatedProj (StatedSp 2 K) :=
  (antiSpEquiv K).trans (projSpEquiv K)

@[expose] noncomputable def autCongr (K : Type) [Field K] [CharP K 2] :
    MulAut (antiSp K) ≃* MulAut (StatedProj (StatedSp 2 K)) :=
  MulAut.congr (antiProjEquiv K)

theorem autCongr_conj (g : antiSp K) :
    autCongr K (MulAut.conj g) = spInner 2 K (antiSpEquiv K g) := by
  rw [autCongr, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, spInner_eq_conj]
  rfl

theorem autCongr_minorAut [Finite K] : autCongr K (minorAut K) = exceptionalAut K :=
  (exceptionalAut_eq_congr (K := K)).symm

theorem autCongr_pow (α : MulAut (antiSp K)) (j : ℕ) : autCongr K (α ^ j) = autCongr K α ^ j :=
  map_pow (autCongr K) α j

theorem mem_inner_iff_autCongr (α : MulAut (antiSp K)) :
    autCongr K α ∈ inner (StatedProj (StatedSp 2 K)) ↔ α ∈ inner (antiSp K) := by
  have h := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr (antiProjEquiv K)
  constructor
  · intro hα
    rw [← h] at hα
    obtain ⟨β, hβ, hβα⟩ := hα
    have : β = α := (autCongr K).injective hβα
    rwa [this] at hβ
  · intro hα
    rw [← h]
    exact ⟨α, hα, rfl⟩

omit [CharP K 2] in
theorem exists_frobenius_data {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ Fr : K ≃+* K, (∀ x, Fr x = x ^ 2) ∧ orderOf Fr = n ∧ Subgroup.zpowers Fr = ⊤ := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  exact ⟨Fr, hFr, hord, hzp⟩

theorem aut_eq_conj_mul_pow [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (antiSp K)) :
    ∃ (g : antiSp K) (j : ℕ), j < 2 * n ∧ α = MulAut.conj g * minorAut K ^ j := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data hn hK
  obtain ⟨-, hall, -⟩ := exceptionalAut_structure hn hFr hord hzp
  obtain ⟨⟨s, j⟩, hsj, -⟩ := hall (autCongr K α)
  refine ⟨(antiSpEquiv K).symm s, j, j.2, (autCongr K).injective ?_⟩
  rw [map_mul, autCongr_conj, MulEquiv.apply_symm_apply, autCongr_pow, autCongr_minorAut]
  exact hsj

theorem involution_eq_conj_mul_pow [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (antiSp K)) (hα : orderOf α = 2) :
    ∃ (g : antiSp K) (j : ℕ), (j = 0 ∨ j = n) ∧ α = MulAut.conj g * minorAut K ^ j := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data hn hK
  have hstruct := exceptionalAut_structure hn hFr hord hzp
  obtain ⟨s, j, hj, hsj⟩ := hstruct.2.2.2.2.2.2.2.2.2 (autCongr K α)
    (by rw [MulEquiv.orderOf_eq]; exact hα)
  refine ⟨(antiSpEquiv K).symm s, j, hj, (autCongr K).injective ?_⟩
  rw [map_mul, autCongr_conj, MulEquiv.apply_symm_apply, autCongr_pow, autCongr_minorAut]
  exact hsj

theorem minorAut_pow_not_mem_inner [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    minorAut K ^ n ∉ inner (antiSp K) := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data hn hK
  obtain ⟨-, -, -, -, -, -, -, -, hmem, -⟩ := exceptionalAut_structure hn hFr hord hzp
  rw [← mem_inner_iff_autCongr, autCongr_pow, autCongr_minorAut, hmem]
  intro h
  have := Nat.le_of_dvd hn h
  omega

theorem conj_injective : Function.Injective (MulAut.conj : antiSp K →* MulAut (antiSp K)) := by
  intro g h hgh
  have h1 : autCongr K (MulAut.conj g) = autCongr K (MulAut.conj h) := by rw [hgh]
  rw [autCongr_conj, autCongr_conj] at h1
  exact (antiSpEquiv K).injective (spInner_injective h1)

end Transport

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem outer_involution_form {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (antiSp K)) (hα : α * α = 1) (hαinn : α ∉ inner (antiSp K)) :
    ∃ g : antiSp K, α = MulAut.conj g * minorAut K ^ n := by
  have h1 : α ≠ 1 := fun h => hαinn (h ▸ one_mem _)
  have hord : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα) h1
  obtain ⟨g, j, hj, hαj⟩ := involution_eq_conj_mul_pow hn hK α hord
  rcases hj with rfl | rfl
  · exact absurd (by rw [hαj, pow_zero, mul_one]; exact ⟨g, rfl⟩) hαinn
  · exact ⟨g, hαj⟩

omit [Finite K] [CharP K 2] in
theorem frobenius_pow_apply {Fr : K ≃+* K} (hFr : ∀ x, Fr x = x ^ 2) (m : ℕ) (t : K) :
    (Fr ^ m) t = t ^ 2 ^ m := by
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, RingAut.mul_apply, hFr, ih, ← pow_mul, pow_succ, mul_comm]

theorem outer_involution_conj_even {n : ℕ} (hn : 2 ≤ n) (hnev : Even n)
    (hK : Nat.card K = 2 ^ n) (α : MulAut (antiSp K)) (hα : α * α = 1)
    (hαinn : α ∉ inner (antiSp K)) :
    ∃ c : antiSp K, α = MulAut.conj c * minorAut K ^ n * (MulAut.conj c)⁻¹ := by
  obtain ⟨g, hg⟩ := outer_involution_form (by omega) hK α hα hαinn
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data (by omega) hK
  obtain ⟨m, hm⟩ := hnev
  set σ : K ≃+* K := Fr ^ m with hσdef
  have hσ : ∀ t, σ t = t ^ 2 ^ m := frobenius_pow_apply hFr m
  have hγ : exceptionalAut K ^ n = fieldAut 2 K σ := by
    rw [hm, ← two_mul, pow_mul, exceptionalAut_sq hFr, ← map_pow]
  have hαP : autCongr K α = spInner 2 K (antiSpEquiv K g) * fieldAut 2 K σ := by
    rw [hg, map_mul, autCongr_conj, autCongr_pow, autCongr_minorAut, hγ]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hαinn
    rw [← mem_inner_iff_autCongr, hαP, h1, map_one, mul_one]
    exact spInner_mem_inner _
  have haa : autCongr K α * autCongr K α = 1 := by rw [← map_mul, hα, map_one]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ :=
    even_symplectic_quadratic_involution_descent (r := 2) (f := n) (by norm_num) (by omega) hK
      (a := autCongr K α) haa (antiSpEquiv K g) σ (by rw [hαP]; rfl) hσ1
  obtain ⟨h, hh⟩ := h
  refine ⟨(antiSpEquiv K).symm h, (autCongr K).injective ?_⟩
  rw [map_mul, map_mul, map_inv, autCongr_conj, MulEquiv.apply_symm_apply, autCongr_pow,
    autCongr_minorAut, hγ]
  exact hh

omit [Finite K] [CharP K 2] in
theorem conj_apply_eq' {G : Type} [Group G] (e : MulAut G) (x : G) :
    MulAut.conj (e x) = e * MulAut.conj x * e⁻¹ := by
  refine MulEquiv.ext fun y => ?_
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_def]

theorem outer_involution_conj_odd {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1))
    (α : MulAut (antiSp K)) (hα : α * α = 1) (hαinn : α ∉ inner (antiSp K)) :
    ∃ c : antiSp K, α = MulAut.conj c * minorAut K ^ (2 * m + 1) * (MulAut.conj c)⁻¹ := by
  obtain ⟨g, hg⟩ := outer_involution_form (by omega) hK α hα hαinn
  set η := minorAut K ^ (2 * m + 1) with hη
  obtain ⟨hηord, hconj, -⟩ := even_symplectic_two_nonsquare_outer_involution_descent m hK
  have hηη : η * η = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one η
    rwa [hηord] at this
  have hgg : g * η g = 1 := by
    apply conj_injective (K := K)
    have h1 : α * α = MulAut.conj (g * η g) := by
      rw [hg, map_mul, conj_apply_eq' η g]
      calc MulAut.conj g * η * (MulAut.conj g * η) =
          MulAut.conj g * (η * MulAut.conj g * η⁻¹) * (η * η) := by group
        _ = _ := by rw [hηη, mul_one]
    rw [← h1, hα, map_one]
  let x : antiSp K ⋊[(Subgroup.zpowers η).subtype] Subgroup.zpowers η :=
    ⟨g, ⟨η, Subgroup.mem_zpowers η⟩⟩
  have hx2 : x ^ 2 = 1 := by
    rw [sq]
    refine SemidirectProduct.ext ?_ ?_
    · show g * η g = 1
      exact hgg
    · exact Subtype.ext hηη
  obtain ⟨h, hh⟩ := hconj x rfl hx2
  have hhl := congrArg SemidirectProduct.left hh
  have hg' : g = h⁻¹ * η h := by
    simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, x] at hhl
    have : h * g * (η h)⁻¹ = 1 := by simpa using hhl
    calc g = h⁻¹ * (h * g * (η h)⁻¹) * η h := by group
      _ = h⁻¹ * η h := by rw [this]; group
  refine ⟨h⁻¹, ?_⟩
  rw [hg, hg', map_mul, conj_apply_eq' η h, map_inv]
  group

theorem outer_involution_conj {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (antiSp K)) (hα : α * α = 1) (hαinn : α ∉ inner (antiSp K)) :
    ∃ c : antiSp K, α = MulAut.conj c * minorAut K ^ n * (MulAut.conj c)⁻¹ := by
  rcases Nat.even_or_odd n with hev | ⟨m, hm⟩
  · exact outer_involution_conj_even hn hev hK α hα hαinn
  · subst hm
    exact outer_involution_conj_odd hK α hα hαinn

end Conj

end CFSG.QuasithinUnique.Setup.X7b
