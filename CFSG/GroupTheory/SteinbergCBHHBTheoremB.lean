module

public import CFSG.GroupTheory.SteinbergCBHHBCoreInduction
public import CFSG.GroupTheory.SteinbergCBHHBGroupReduction
public import CFSG.GroupTheory.SteinbergCBHHBNumberTheory

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Module Polynomial Subgroup

section MinPoly

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

theorem minpoly_eq_X_sub_one_pow (X₀ : Module.End F W) {r : ℕ} (hr : (X₀ - 1) ^ r = 0)
    (hmin : ∀ j, (X₀ - 1) ^ j = 0 → r ≤ j) : minpoly F X₀ = (X - 1) ^ r := by
  have hann : aeval X₀ ((X - 1 : F[X]) ^ r) = 0 := by
    rw [map_pow, map_sub, aeval_X, map_one, hr]
  have hint : IsIntegral F X₀ := Algebra.IsIntegral.isIntegral X₀
  have hdvd : minpoly F X₀ ∣ (X - 1 : F[X]) ^ r := minpoly.dvd F X₀ hann
  have hprime : Prime (X - 1 : F[X]) := by
    have := prime_X_sub_C (1 : F)
    rwa [map_one] at this
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hprime r).1 hdvd
  have hmonic : ((X - 1 : F[X]) ^ i).Monic := by
    have := (monic_X_sub_C (1 : F)).pow i
    rwa [map_one] at this
  have heq := eq_of_monic_of_associated (minpoly.monic hint) hmonic hassoc
  have hi' : r ≤ i := by
    apply hmin
    have := minpoly.aeval F X₀
    rwa [heq, map_pow, map_sub, aeval_X, map_one] at this
  rw [heq, le_antisymm hi hi']

end MinPoly

section BaseChange

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

@[expose] def baseChangeHom (K : Type*) [Field K] [Algebra F K] :
    Module.End F V →+* Module.End K (Fin (finrank F V) → K) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin (finrank F V)) (Fin (finrank F V)) K ≃ₐ[K]
      Module.End K (Fin (finrank F V) → K)).toRingEquiv.toRingHom.comp
    ((algebraMap F K).mapMatrix.comp
      (LinearMap.toMatrixAlgEquiv (Module.finBasis F V)).toRingEquiv.toRingHom)

theorem baseChangeHom_injective (K : Type*) [Field K] [Algebra F K] :
    Function.Injective (baseChangeHom (F := F) (V := V) K) := by
  intro f g h
  have h1 : (algebraMap F K).mapMatrix (LinearMap.toMatrixAlgEquiv (Module.finBasis F V) f) =
      (algebraMap F K).mapMatrix (LinearMap.toMatrixAlgEquiv (Module.finBasis F V) g) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin (finrank F V)) (Fin (finrank F V)) K ≃ₐ[K]
      Module.End K (Fin (finrank F V) → K)).injective h
  exact (LinearMap.toMatrixAlgEquiv (Module.finBasis F V)).injective
    (Matrix.map_injective (algebraMap F K).injective h1)

variable {p : ℕ} [Fact p.Prime] [CharP F p]

omit [CharP F p] in
theorem hh_core_of_baseChange (K : Type*) [Field K] [Algebra F K] [IsAlgClosed K] [CharP K p]
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (Q : Subgroup (Module.End F V)ˣ) [Finite Q]
    (hQq : IsPGroup q Q) (x : (Module.End F V)ˣ) {n : ℕ} (hn : 1 ≤ n)
    (hxQ : x ∈ normalizer (Q : Set (Module.End F V)ˣ)) (hxn : x ^ (p ^ n) = 1)
    (hz : ∃ a ∈ Q, x ^ (p ^ (n - 1)) * a ≠ a * x ^ (p ^ (n - 1))) :
    HHConclusion F p q Q x n := by
  set Ψ := baseChangeHom (F := F) (V := V) K with hΨ
  set ι := Units.map (Ψ : Module.End F V →* Module.End K (Fin (finrank F V) → K)) with hιdef
  have hιinj : Function.Injective ι := Units.map_injective (baseChangeHom_injective K)
  have hιx : ∀ y : (Module.End F V)ˣ, ((ι y : (Module.End K (Fin (finrank F V) → K))ˣ) :
      Module.End K (Fin (finrank F V) → K)) = Ψ (y : Module.End F V) := fun _ => rfl
  have : Finite (Q.map ι) := by
    have h1 : ((Q.map ι : Subgroup _) : Set (Module.End K (Fin (finrank F V) → K))ˣ).Finite := by
      rw [Subgroup.coe_map]
      exact (Set.toFinite _).image _
    exact h1.to_subtype
  have hxQ' : ι x ∈
      normalizer ((Q.map ι : Subgroup _) : Set (Module.End K (Fin (finrank F V) → K))ˣ) :=
    le_normalizer_map ι (mem_map_of_mem ι hxQ)
  have hxn' : ι x ^ (p ^ n) = 1 := by rw [← map_pow, hxn, map_one]
  have hz' : ∃ a ∈ Q.map ι, ι x ^ (p ^ (n - 1)) * a ≠ a * ι x ^ (p ^ (n - 1)) := by
    obtain ⟨a, ha, hne⟩ := hz
    refine ⟨ι a, mem_map_of_mem ι ha, fun h => hne (hιinj ?_)⟩
    rw [map_mul, map_mul, map_pow]
    exact h
  have hpull : ∀ j, (((ι x : (Module.End K (Fin (finrank F V) → K))ˣ) :
      Module.End K (Fin (finrank F V) → K)) - 1) ^ j ≠ 0 →
      ((x : Module.End F V) - 1) ^ j ≠ 0 := by
    intro j hj h0
    apply hj
    rw [hιx, ← map_one Ψ, ← map_sub, ← map_pow, h0, map_zero]
  rcases hh_core (K := K) (p := p) hqp (Q.map ι) (hQq.map ι) (ι x) hn hxQ' hxn' hz' with h |
    ⟨m, k, hm, hmn, hk, hkq, ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, hab⟩, h⟩
  · exact Or.inl (hpull _ h)
  · exact Or.inr ⟨m, k, hm, hmn, hk, hkq,
      ⟨a', ha', b', hb', fun h' => hab (by rw [← map_mul, h', map_mul])⟩, hpull _ h⟩

theorem hh_core_field {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (Q : Subgroup (Module.End F V)ˣ)
    [Finite Q] (hQq : IsPGroup q Q) (x : (Module.End F V)ˣ) {n : ℕ} (hn : 1 ≤ n)
    (hxQ : x ∈ normalizer (Q : Set (Module.End F V)ˣ)) (hxn : x ^ (p ^ n) = 1)
    (hz : ∃ a ∈ Q, x ^ (p ^ (n - 1)) * a ≠ a * x ^ (p ^ (n - 1))) :
    HHConclusion F p q Q x n :=
  hh_core_of_baseChange (AlgebraicClosure F) hqp Q hQq x hn hxQ hxn hz

end BaseChange

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem sylow_nonabelian_of_le {q : ℕ} [Fact q.Prime] {S : Subgroup G} (hS : IsPGroup q S)
    (hnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) (P : Sylow q G) :
    ∃ a ∈ (P : Subgroup G), ∃ b ∈ (P : Subgroup G), a * b ≠ b * a := by
  obtain ⟨P₀, hP₀⟩ := hS.exists_le_sylow
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P₀ P
  have hmem : ∀ c ∈ (P₀ : Subgroup G), g * c * g⁻¹ ∈ ((g • P₀ : Sylow q G) : Subgroup G) := by
    intro c hc
    rw [Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul c (MulAut.conj g) (P₀ : Subgroup G) hc
    rwa [MulAut.smul_def, MulAut.conj_apply] at this
  refine ⟨g * a * g⁻¹, hmem a (hP₀ ha), g * b * g⁻¹, hmem b (hP₀ hb), fun h => hab ?_⟩
  have h1 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := h
      _ = g * (b * a) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h1)

end Sylow

section Main

open CFSG.HallHigman

variable {p : ℕ} [hp : Fact p.Prime] {F : Type*} [Field F] [CharP F p] {V : Type*}
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem hall_higman_theorem_B_minimal_polynomial
    (G : Subgroup (LinearMap.GeneralLinearGroup F V)) [Finite G] (hG : IsPSolvable p G)
    (hO : CFSG.piCore {q : Nat.Primes | q.val = p} G = ⊥) (x : G) {n : ℕ} (hn : 1 ≤ n)
    (hx : orderOf x = p ^ n) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ p ^ n ∧
      minpoly F ((x : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) = (X - 1) ^ r ∧
      (r < p ^ n → ∃ n₀ q k : ℕ, 1 ≤ n₀ ∧ n₀ ≤ n ∧ q.Prime ∧ 1 ≤ k ∧ p ^ n₀ - 1 = q ^ k ∧
        (∀ S : Sylow q G, ∃ a ∈ (S : Subgroup G), ∃ b ∈ (S : Subgroup G), a * b ≠ b * a) ∧
        p ^ (n - n₀) * (p ^ n₀ - 1) ≤ r) ∧
      (r < p ^ n →
        ((∃ j, p = Nat.fermatNumber j) ∧
          (∀ S : Sylow 2 G, ∃ a ∈ (S : Subgroup G), ∃ b ∈ (S : Subgroup G), a * b ≠ b * a) ∧
          p ^ n - p ^ (n - 1) ≤ r) ∨
        (p = 2 ∧ ∃ m, m ≤ n ∧ (mersenne m).Prime ∧
          (∀ S : Sylow (mersenne m) G, ∃ a ∈ (S : Subgroup G), ∃ b ∈ (S : Subgroup G),
            a * b ≠ b * a) ∧
          2 ^ n - 2 ^ (n - m) ≤ r)) ∧
      (5 ≤ p → (((x : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) - 1) ^ 2 ≠ 0) := by
  classical
  set X₀ : V →ₗ[F] V := ((x : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) with hX₀
  have hp2 := hp.out.two_le
  have hxpn : x ^ (p ^ n) = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hxpn' : (x : LinearMap.GeneralLinearGroup F V) ^ (p ^ n) = 1 := by
    rw [← Subgroup.coe_pow, hxpn]
    rfl
  have hX₀pn : X₀ ^ (p ^ n) = 1 := by
    rw [hX₀, ← Units.val_pow_eq_pow_val, hxpn', Units.val_one]
  have hN : (X₀ - 1) ^ (p ^ n) = 0 := by
    rw [sub_one_pow_char_pow (p := p) X₀ n, hX₀pn, sub_self]
  have hex : ∃ k, (X₀ - 1) ^ k = 0 := ⟨p ^ n, hN⟩
  set r := Nat.find hex with hrdef
  have hr : (X₀ - 1) ^ r = 0 := Nat.find_spec hex
  have hmin : ∀ j, (X₀ - 1) ^ j = 0 → r ≤ j := fun j hj => Nat.find_min' hex hj
  have hrle : r ≤ p ^ n := hmin _ hN
  have hlt : ∀ j, (X₀ - 1) ^ j ≠ 0 → j < r := by
    intro j hj
    by_contra hle
    push Not at hle
    apply hj
    rw [← Nat.sub_add_cancel hle, pow_add, hr, mul_zero]
  have hpn : p ≤ p ^ n := Nat.le_self_pow (by omega) p
  have hr1 : 1 ≤ r := by
    by_contra h0
    have h0' : r = 0 := by omega
    have h1 : (1 : V →ₗ[F] V) = 0 := by
      have := hr
      rwa [h0', pow_zero] at this
    have hall : ∀ f : V →ₗ[F] V, f = 0 := fun f => by
      rw [← one_mul f, h1, zero_mul]
    have hx1 : x = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hall ((x : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V),
        hall (((1 : G) : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V)]
    rw [hx1, orderOf_one] at hx
    omega
  have hminpoly : minpoly F X₀ = (X - 1) ^ r := minpoly_eq_X_sub_one_pow X₀ hr hmin
  obtain ⟨q, hqprime, hqp, S, hSq, hxS, a₀, ha₀S, ha₀⟩ :=
    exists_invariant_qsubgroup_not_centralized hG hO x hn hx
  have : Fact q.Prime := ⟨hqprime⟩
  have : Finite (S.map G.subtype) := by
    have h1 : ((S.map G.subtype : Subgroup _) :
        Set (LinearMap.GeneralLinearGroup F V)).Finite := by
      rw [Subgroup.coe_map]
      exact (Set.toFinite _).image _
    exact h1.to_subtype
  have hcore := hh_core_field hqp (S.map G.subtype) (hSq.map G.subtype)
    (x : LinearMap.GeneralLinearGroup F V) hn
    (le_normalizer_map G.subtype (mem_map_of_mem G.subtype hxS)) hxpn'
    ⟨(a₀ : LinearMap.GeneralLinearGroup F V), mem_map_of_mem G.subtype ha₀S, fun h => ha₀
      (Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using h))⟩
  rcases hcore with hA | ⟨m, k, hm1, hmn, hk1, hpq, ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, hab⟩,
    hB⟩
  ·
    have hrp : r = p ^ n := by
      have := hlt _ hA
      omega
    refine ⟨r, hr1, hrle, hminpoly, fun h => absurd hrp (ne_of_lt h),
      fun h => absurd hrp (ne_of_lt h), fun hp5 h2 => ?_⟩
    have := hmin 2 h2
    omega
  ·
    have hSnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a :=
      ⟨a', ha', b', hb', fun h => hab (by rw [← map_mul, h, map_mul])⟩
    have hsyl := sylow_nonabelian_of_le hSq hSnab
    have hqk : 2 ≤ q ^ k := le_trans hqprime.two_le (Nat.le_self_pow (by omega) q)
    have hpm : p ≤ p ^ m := Nat.le_self_pow (by omega) p
    have hpnm : 0 < p ^ (n - m) := pow_pos hp.out.pos _
    have h3 : p ^ m - 1 ≤ p ^ (n - m) * (p ^ m - 1) := Nat.le_mul_of_pos_left _ hpnm
    have hbound : p ^ (n - m) * (p ^ m - 1) ≤ r := by
      have h1 := hlt _ hB
      generalize p ^ (n - m) * (p ^ m - 1) = D at h1 h3
      omega
    have hid : p ^ (n - m) * (p ^ m - 1) = p ^ n - p ^ (n - m) := by
      rw [Nat.mul_sub_one, ← pow_add, Nat.sub_add_cancel hmn]
    refine ⟨r, hr1, hrle, hminpoly, fun _ => ⟨m, q, k, hm1, hmn, hqprime, hk1, hpq, hsyl,
      hbound⟩, fun _ => ?_, fun hp5 h2 => ?_⟩
    · by_cases hp2' : p = 2
      ·
        right
        have hpq' : 2 ^ m - 1 = q ^ k := hp2' ▸ hpq
        obtain ⟨rfl, -, rfl⟩ := two_pow_sub_one_eq_prime_pow hqprime hk1 hpq'
        refine ⟨hp2', m, hmn, hqprime, hsyl, ?_⟩
        have := hid ▸ hbound
        rwa [hp2'] at this
      ·
        left
        obtain ⟨rfl, hferm, hcase⟩ := odd_pow_sub_one_eq_prime_pow hp.out hp2' hm1 hqprime hk1 hpq
        refine ⟨hferm, hsyl, ?_⟩
        rcases hcase with rfl | ⟨hp3, rfl⟩
        · exact hid ▸ hbound
        ·
          have e1 : p ^ n = p ^ (n - 2) * 9 := by
            rw [← show p ^ 2 = 9 by rw [hp3]; norm_num, ← pow_add, Nat.sub_add_cancel hmn]
          have e2 : p ^ (n - 1) = p ^ (n - 2) * 3 := by
            rw [← hp3, ← pow_succ, show n - 2 + 1 = n - 1 by omega]
          have e3 : p ^ 2 - 1 = 8 := by rw [hp3]; norm_num
          rw [e3] at hbound
          rw [e1, e2]
          generalize p ^ (n - 2) = t at hbound ⊢
          omega
    ·
      have := hmin 2 h2
      generalize p ^ (n - m) * (p ^ m - 1) = D at hbound h3
      generalize p ^ m = P at h3 hpm
      omega

end Main

end CFSG.GroupTheory.HallHigmanB
