module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Module

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem pow_apply_eq_add_of_fix {x : V ≃ₗ[K] V} {u : V} (hv : x (x u - u) = x u - u) (k : ℕ) :
    (x ^ k) u = u + k • (x u - u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, hv, succ_nsmul]
    abel

theorem ker_inf_range_sub_one_eq_bot {x : V ≃ₗ[K] V} {ℓ : ℕ} (hx : x ^ ℓ = 1)
    (hℓ : (ℓ : K) ≠ 0) :
    LinearMap.ker ((x : V →ₗ[K] V) - 1) ⊓ LinearMap.range ((x : V →ₗ[K] V) - 1) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv1, u, rfl⟩
  rw [Submodule.mem_bot]
  have hv1' : x (x u - u) = x u - u := by
    have h := LinearMap.mem_ker.mp hv1
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply] at h
    exact sub_eq_zero.mp h
  have h0 := pow_apply_eq_add_of_fix hv1' ℓ
  rw [hx] at h0
  have h1 : u = u + ℓ • (x u - u) := h0
  have h2 : (ℓ : K) • (x u - u) = 0 := by
    rw [Nat.cast_smul_eq_nsmul K]
    have := congrArg (fun w => w - u) h1
    simpa using this.symm
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
  exact (smul_eq_zero.mp h2).resolve_left hℓ


theorem not_dvd_card_sp_of_prime {q ℓ m : ℕ} (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q)
    (hord : ∀ j, 1 ≤ j → j ≤ m → ¬ ℓ ∣ q ^ (2 * j) - 1) :
    ¬ ℓ ∣ q ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (q ^ (2 * j) - 1) := by
  intro h
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h1 | h1
  · exact hℓq (hℓ.dvd_of_dvd_pow h1)
  · obtain ⟨j, hj, hj'⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 h1
    have := Finset.mem_Icc.1 hj
    exact hord j this.1 this.2 hj'

variable [FiniteDimensional K V]

theorem ker_sub_one_eq_bot_of_isometry [Finite K] {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n) {x : V ≃ₗ[K] V}
    (hxB : ∀ a b, B (x a) (x b) = B a b) {ℓ : ℕ} (hℓ : ℓ.Prime) (hx : x ^ ℓ = 1) (hx1 : x ≠ 1)
    (hℓK : (ℓ : K) ≠ 0) (hℓq : ¬ ℓ ∣ Nat.card K)
    (hord : ∀ j, 1 ≤ j → j < n → ¬ ℓ ∣ Nat.card K ^ (2 * j) - 1) :
    LinearMap.ker ((x : V →ₗ[K] V) - 1) = ⊥ := by
  set C := LinearMap.ker ((x : V →ₗ[K] V) - 1) with hC
  set D := LinearMap.range ((x : V →ₗ[K] V) - 1) with hD
  have hCD := ker_inf_range_sub_one_eq_bot hx hℓK
  have hdims : finrank K D + finrank K C = finrank K V :=
    LinearMap.finrank_range_add_finrank_ker ((x : V →ₗ[K] V) - 1)
  have hsup : C ⊔ D = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq C D
    rw [hCD, finrank_bot] at this
    omega
  have hmemC : ∀ c ∈ C, x c = c := fun c hc => by
    have h := LinearMap.mem_ker.mp hc
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply] at h
    exact sub_eq_zero.mp h
  have horth : ∀ c ∈ C, ∀ d ∈ D, B c d = 0 := by
    rintro c hc _ ⟨u, rfl⟩
    have h := hxB c u
    rw [hmemC c hc] at h
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub, h,
      sub_self]
  have hDnd : (B.restrict D).Nondegenerate := by
    refine LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hB.isRefl ?_
    rw [Submodule.disjoint_def]
    intro d hdD hdO
    apply hnd.2 d
    intro v
    have hv : v ∈ C ⊔ D := hsup ▸ Submodule.mem_top
    obtain ⟨c, hc, d', hd', rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, LinearMap.add_apply, horth c hc d hdD, zero_add]
    exact hdO d' hd'
  have hDalt : (B.restrict D).IsAlt := fun d => hB d
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank hDalt hDnd
  have hmap : D.map (x : V →ₗ[K] V) = D := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨x u, ?_⟩
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub]
    · rintro _ ⟨u, rfl⟩
      refine ⟨((x : V →ₗ[K] V) - 1) (x.symm u), ⟨x.symm u, rfl⟩, ?_⟩
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub,
        LinearEquiv.apply_symm_apply]
  set xD := x.ofSubmodules D D hmap with hxD
  have hpow : ∀ (k : ℕ) (d : D), (((xD ^ k) d : D) : V) = (x ^ k) d := by
    intro k
    induction k with
    | zero => intro d; rfl
    | succ k ih =>
      intro d
      rw [pow_succ', LinearEquiv.mul_apply, pow_succ', LinearEquiv.mul_apply]
      change x (((xD ^ k) d : D) : V) = _
      rw [ih]
  have hxDmem : xD ∈ TauCeti.BilinForm.isometryGroup (B.restrict D) :=
    TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun a b => hxB a b
  set y : TauCeti.BilinForm.isometryGroup (B.restrict D) := ⟨xD, hxDmem⟩ with hy
  have hyℓ : y ^ ℓ = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro d
    apply Subtype.ext
    rw [Subgroup.coe_pow, hpow ℓ d, hx]
    rfl
  by_contra hCne
  have hC1 : 1 ≤ finrank K C := by
    rcases Nat.eq_zero_or_pos (finrank K C) with h | h
    · exact absurd (Submodule.finrank_eq_zero.mp h) hCne
    · exact h
  have hmn : m < n := by omega
  have hcard := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup m
    (B.restrict D) hDalt hDnd (by omega)
  have hy1 : y = 1 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hyℓ
    rcases (Nat.dvd_prime hℓ).1 hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have h2 := orderOf_dvd_natCard y
      rw [h1, hcard] at h2
      exact not_dvd_card_sp_of_prime hℓ hℓq (fun j hj hjm => hord j hj (by omega)) h2
  have hxDfix : ∀ d ∈ D, x d = d := by
    intro d hd
    have h1 := congrArg (fun z : TauCeti.BilinForm.isometryGroup (B.restrict D) =>
      (((z : D ≃ₗ[K] D) ⟨d, hd⟩ : D) : V)) hy1
    simpa [hy, hxD] using h1
  apply hx1
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ C ⊔ D := hsup ▸ Submodule.mem_top
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hmemC c hc, hxDfix d hd]
  rfl


theorem exists_apply_ne_of_isometry [Finite K] {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n) {x : V ≃ₗ[K] V}
    (hxB : ∀ a b, B (x a) (x b) = B a b) {ℓ : ℕ} (hℓ : ℓ.Prime) (hx : x ^ ℓ = 1) (hx1 : x ≠ 1)
    (hℓK : (ℓ : K) ≠ 0) (hℓq : ¬ ℓ ∣ Nat.card K)
    (hord : ∀ j, 1 ≤ j → j < n → ¬ ℓ ∣ Nat.card K ^ (2 * j) - 1) {U : Submodule K V}
    (hU : U ≠ ⊥) : ∃ u ∈ U, x u ≠ u := by
  by_contra h
  push Not at h
  apply hU
  rw [eq_bot_iff, ← ker_sub_one_eq_bot_of_isometry hB hnd hdim hxB hℓ hx hx1 hℓK hℓq hord]
  intro u hu
  rw [LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, h u hu, sub_self]


omit [FiniteDimensional K V] in
theorem natCard_linearEquiv_self_eq [Fintype K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] :
    Nat.card (U ≃ₗ[K] U) = ∏ i : Fin (finrank K U),
      (Fintype.card K ^ finrank K U - Fintype.card K ^ (i : ℕ)) := by
  rw [← Matrix.card_GL_field]
  exact Nat.card_congr ((LinearMap.GeneralLinearGroup.generalLinearEquiv K U).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K U)).toMulEquiv)).toEquiv

theorem not_dvd_prod_pow_sub_pow {q ℓ d : ℕ} (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q)
    (hord : ∀ j, 1 ≤ j → j ≤ d → ¬ ℓ ∣ q ^ j - 1) :
    ¬ ℓ ∣ ∏ i : Fin d, (q ^ d - q ^ (i : ℕ)) := by
  intro h
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 h
  have hid : (i : ℕ) < d := i.2
  have hfac : q ^ d - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (d - i) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hid.le]
  rw [hfac] at hi
  rcases (Nat.Prime.dvd_mul hℓ).1 hi with h1 | h1
  · exact hℓq (hℓ.dvd_of_dvd_pow h1)
  · exact hord (d - i) (by omega) (by omega) h1

theorem le_finrank_of_isometry [Finite K] {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n) {x : V ≃ₗ[K] V}
    (hxB : ∀ a b, B (x a) (x b) = B a b) {ℓ : ℕ} (hℓ : ℓ.Prime) (hx : x ^ ℓ = 1) (hx1 : x ≠ 1)
    (hℓK : (ℓ : K) ≠ 0) (hℓq : ¬ ℓ ∣ Nat.card K)
    (hord : ∀ j, 1 ≤ j → j < n → ¬ ℓ ∣ Nat.card K ^ (2 * j) - 1)
    (hord' : ∀ i, 1 ≤ i → i < n → ¬ ℓ ∣ Nat.card K ^ i - 1) {U : Submodule K V}
    (hU : U ≠ ⊥) (hUx : ∀ u ∈ U, x u ∈ U) : n ≤ finrank K U := by
  classical
  have := Fintype.ofFinite K
  by_contra hlt
  push Not at hlt
  have hmapU : U.map (x : V →ₗ[K] V) = U := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq x U)
    rintro _ ⟨u, hu, rfl⟩
    exact hUx u hu
  set xU := x.ofSubmodules U U hmapU with hxU
  have hpow : ∀ (k : ℕ) (u : U), (((xU ^ k) u : U) : V) = (x ^ k) u := by
    intro k
    induction k with
    | zero => intro u; rfl
    | succ k ih =>
      intro u
      rw [pow_succ', LinearEquiv.mul_apply, pow_succ', LinearEquiv.mul_apply]
      change x (((xU ^ k) u : U) : V) = _
      rw [ih]
  have hxUℓ : xU ^ ℓ = 1 := by
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    rw [hpow ℓ u, hx]
    rfl
  obtain ⟨u, hu, hxu⟩ := exists_apply_ne_of_isometry hB hnd hdim hxB hℓ hx hx1 hℓK hℓq hord hU
  have hxU1 : xU ≠ 1 := by
    intro h
    apply hxu
    have := congrArg (fun z : U ≃ₗ[K] U => ((z ⟨u, hu⟩ : U) : V)) h
    simpa [hxU] using this
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hordU : orderOf xU = ℓ := orderOf_eq_prime hxUℓ hxU1
  have hfin : Finite (U ≃ₗ[K] U) := by
    apply Finite.of_equiv _ ((LinearMap.GeneralLinearGroup.generalLinearEquiv K U).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K U)).toMulEquiv)).toEquiv.symm
  have hdvd := orderOf_dvd_natCard xU
  rw [hordU, natCard_linearEquiv_self_eq U, ← Nat.card_eq_fintype_card] at hdvd
  exact not_dvd_prod_pow_sub_pow hℓ hℓq
    (fun j hj hjd => hord' j hj (by omega)) hdvd

end CFSG.SeitzReduction.SymplecticPilot
