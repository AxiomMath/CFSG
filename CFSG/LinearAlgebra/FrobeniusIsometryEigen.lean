module

public import CFSG.LinearAlgebra.FrobeniusIsometryQuadratic

public section

namespace CFSG.LinearAlgebra

open Module

namespace FrobeniusIsometryEigen

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def avg (n : ℕ) (z : V ≃ₗ[K] V) : V →ₗ[K] V :=
  ∑ i ∈ Finset.range n, ((z ^ i : V ≃ₗ[K] V) : V →ₗ[K] V)

theorem avg_apply (n : ℕ) (z : V ≃ₗ[K] V) (v : V) :
    avg n z v = ∑ i ∈ Finset.range n, (z ^ i) v := by
  simp only [avg, LinearMap.sum_apply, LinearEquiv.coe_coe]

theorem one_apply' (v : V) : (1 : V ≃ₗ[K] V) v = v := rfl

theorem pow_apply_of_fixed {z : V ≃ₗ[K] V} {v : V} (hv : z v = v) (i : ℕ) : (z ^ i) v = v := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hv]

theorem apply_avg {n : ℕ} {z : V ≃ₗ[K] V} (hz : z ^ n = 1) (v : V) :
    z (avg n z v) = avg n z v := by
  rw [avg_apply, map_sum]
  have h1 : ∀ i, z ((z ^ i) v) = (z ^ (i + 1)) v := fun i => by
    rw [pow_succ', LinearEquiv.mul_apply]
  simp only [h1]
  have h2 := Finset.sum_range_succ' (fun i => (z ^ i) v) n
  have h3 := Finset.sum_range_succ (fun i => (z ^ i) v) n
  rw [hz] at h3
  exact add_right_cancel (h2.symm.trans h3)

theorem avg_apply_of_fixed {n : ℕ} {z : V ≃ₗ[K] V} {v : V} (hv : z v = v) :
    avg n z v = n • v := by
  rw [avg_apply]
  simp only [pow_apply_of_fixed hv, Finset.sum_const, Finset.card_range]

theorem avg_comm {n : ℕ} {z x : V ≃ₗ[K] V} (hxz : x * z = z * x) (v : V) :
    x (avg n z v) = avg n z (x v) := by
  rw [avg_apply, avg_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ((Commute.pow_right hxz i).eq)]

theorem exists_ne_one_fixed_moved {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {E : Subgroup (V ≃ₗ[K] V)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) {x₀ y₀ : V ≃ₗ[K] V} (hx₀ : x₀ ∈ E) (hy₀ : y₀ ∈ E)
    (hx₀1 : x₀ ≠ 1) (hy₀x : ∀ a : ℕ, x₀ ^ a * y₀ ≠ 1) :
    ∃ z ∈ E, z ≠ 1 ∧ ∃ w ∈ E, ∃ v, z v = v ∧ w v ≠ v := by
  classical
  have := Fact.mk hp
  by_contra hcon
  push Not at hcon
  let F := FrobeniusIsometry.fixSub E
  have havgF : ∀ z ∈ E, z ≠ 1 → ∀ v, avg p z v ∈ F := fun z hz hz1 v =>
    FrobeniusIsometry.mem_fixSub.mpr fun w hw => hcon z hz hz1 w hw _ (apply_avg (hexp z hz) v)
  have hord : orderOf x₀ = p := orderOf_eq_prime (hexp x₀ hx₀) hx₀1
  have hx₀i : ∀ i ∈ Finset.range p, i ≠ 0 → x₀ ^ i ≠ 1 := fun i hi hi0 h1 => by
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at this
    exact hi0 (Nat.eq_zero_of_dvd_of_lt this (Finset.mem_range.mp hi))
  have hpv : ∀ v, (p : K) • v ∈ F := by
    intro v
    have hpow : ∀ a i : ℕ, ((x₀ ^ a * y₀) ^ i) v = ((x₀ ^ i) ^ a) ((y₀ ^ i) v) := by
      intro a i
      have hc : Commute (x₀ ^ a) y₀ := Commute.pow_left (hcomm x₀ hx₀ y₀ hy₀) a
      rw [hc.mul_pow, ← pow_mul, mul_comm a i, pow_mul, LinearEquiv.mul_apply]
    have hsum : ∑ a ∈ Finset.range p, avg p (x₀ ^ a * y₀) v =
        ∑ i ∈ Finset.range p, avg p (x₀ ^ i) ((y₀ ^ i) v) := by
      simp only [avg_apply, hpow]
      exact Finset.sum_comm
    have hL : ∑ a ∈ Finset.range p, avg p (x₀ ^ a * y₀) v ∈ F :=
      F.sum_mem fun a _ => havgF _ (E.mul_mem (E.pow_mem hx₀ a) hy₀) (hy₀x a) v
    have hR : ∑ i ∈ Finset.range p, avg p (x₀ ^ i) ((y₀ ^ i) v) =
        (p : K) • v + ∑ i ∈ (Finset.range p).erase 0, avg p (x₀ ^ i) ((y₀ ^ i) v) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hp.pos), pow_zero, pow_zero,
        avg_apply_of_fixed (z := (1 : V ≃ₗ[K] V)) rfl, one_apply', Nat.cast_smul_eq_nsmul]
    have hE : ∑ i ∈ (Finset.range p).erase 0, avg p (x₀ ^ i) ((y₀ ^ i) v) ∈ F :=
      F.sum_mem fun i hi => havgF _ (E.pow_mem hx₀ i)
        (hx₀i i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)) _
    rw [hsum, hR] at hL
    simpa using F.sub_mem hL hE
  apply hx₀1
  refine LinearEquiv.ext fun v => ?_
  have h1 := FrobeniusIsometry.mem_fixSub.mp (hpv v) x₀ hx₀
  rw [map_smul] at h1
  exact (smul_right_injective V hpK h1 : _)

@[expose] noncomputable def part (e : V →ₗ[K] V) (x : V ≃ₗ[K] V) : V →ₗ[K] V :=
  (x : V →ₗ[K] V) ∘ₗ (LinearMap.id - e) + e

theorem part_apply (e : V →ₗ[K] V) (x : V ≃ₗ[K] V) (v : V) :
    part e x v = x (v - e v) + e v := rfl

variable {e : V →ₗ[K] V}

theorem e_part (he : ∀ v, e (e v) = e v) {x : V ≃ₗ[K] V} (hx : ∀ v, x (e v) = e (x v))
    (v : V) : e (part e x v) = e v := by
  rw [part_apply, map_add, ← hx, map_sub, he, sub_self, map_zero, zero_add]

theorem part_part (he : ∀ v, e (e v) = e v) {x y : V ≃ₗ[K] V} (hy : ∀ v, y (e v) = e (y v))
    (v : V) : part e x (part e y v) = x (y (v - e v)) + e v := by
  rw [part_apply e x, e_part he hy, part_apply e y, add_sub_cancel_right]

theorem symm_comm {x : V ≃ₗ[K] V} (hx : ∀ v, x (e v) = e (x v)) (v : V) :
    x.symm (e v) = e (x.symm v) :=
  x.injective (by rw [LinearEquiv.apply_symm_apply, hx, LinearEquiv.apply_symm_apply])

@[expose] noncomputable def partEquiv (e : V →ₗ[K] V) (he : ∀ v, e (e v) = e v) (x : V ≃ₗ[K] V)
    (hx : ∀ v, x (e v) = e (x v)) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (part e x) (part e x.symm)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, part_part he (symm_comm hx), LinearEquiv.apply_symm_apply,
        sub_add_cancel, LinearMap.id_apply])
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, part_part he hx, LinearEquiv.symm_apply_apply, sub_add_cancel,
        LinearMap.id_apply])

theorem partEquiv_apply (he : ∀ v, e (e v) = e v) (x : V ≃ₗ[K] V)
    (hx : ∀ v, x (e v) = e (x v)) (v : V) : partEquiv e he x hx v = x (v - e v) + e v := rfl

theorem partEquiv_pow_apply (he : ∀ v, e (e v) = e v) (x : V ≃ₗ[K] V)
    (hx : ∀ v, x (e v) = e (x v)) (n : ℕ) (v : V) :
    (partEquiv e he x hx ^ n) v = (x ^ n) (v - e v) + e v := by
  have hxn : ∀ m : ℕ, ∀ v, (x ^ m) (e v) = e ((x ^ m) v) := fun m => by
    induction m with
    | zero => intro v; rfl
    | succ m ih => intro v; rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih, hx]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih]
    have h := part_part he (hxn n) v (x := x)
    rw [part_apply e (x ^ n)] at h
    rw [partEquiv_apply, ← part_apply, h, pow_succ', LinearEquiv.mul_apply]

theorem partEquiv_comm (he : ∀ v, e (e v) = e v) (x : V ≃ₗ[K] V)
    (hx : ∀ v, x (e v) = e (x v)) {c : V ≃ₗ[K] V} (hcx : c * x = x * c)
    (hce : ∀ v, c (e v) = e (c v)) : c * partEquiv e he x hx = partEquiv e he x hx * c := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, partEquiv_apply, partEquiv_apply, map_add,
    ← LinearEquiv.mul_apply, hcx, LinearEquiv.mul_apply, map_sub, hce]

theorem partEquiv_mem_orthogonalGroup (he : ∀ v, e (e v) = e v) {Q : QuadraticForm K V}
    (hperp : ∀ u w, e u = 0 → e w = w → QuadraticMap.polar Q u w = 0) {x : V ≃ₗ[K] V}
    (hx : ∀ v, x (e v) = e (x v)) (hxQ : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    partEquiv e he x hx ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  have hQx := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hxQ
  have hpol : ∀ a b, Q (a + b) = Q a + Q b + QuadraticMap.polar Q a b := fun a b => by
    unfold QuadraticMap.polar
    ring
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  have hk : e (v - e v) = 0 := by rw [map_sub, he, sub_self]
  have hk' : e (x (v - e v)) = 0 := by rw [← hx, hk, map_zero]
  rw [partEquiv_apply, hpol, hperp _ _ hk' (he v), hQx, add_zero]
  conv_rhs => rw [← sub_add_cancel v (e v), hpol, hperp _ _ hk (he v), add_zero]

theorem conj_pow_eq_pow_pow {G : Type*} [Group G] {g : G} {S : Subgroup G} {k : ℕ}
    (h : ∀ s ∈ S, g * s * g⁻¹ = s ^ k) (a : ℕ) :
    ∀ s ∈ S, g ^ a * s * (g ^ a)⁻¹ = s ^ (k ^ a) := by
  induction a with
  | zero => intro s _; simp
  | succ a ih =>
    intro s hs
    have h1 : g ^ (a + 1) * s * (g ^ (a + 1))⁻¹ = g * (g ^ a * s * (g ^ a)⁻¹) * g⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      simp only [mul_assoc]
    rw [h1, ih s hs, ← conj_pow, h s hs, ← pow_mul, pow_succ' k a]

theorem pow_eq_self_of_mul {G : Type*} [Group G] {S T : Subgroup G}
    (hST : ∀ c ∈ S, c ∈ T → c = 1) {a b : G} (ha : a ∈ S) (hb : b ∈ T) {n m : ℕ}
    (h : a ^ n * b ^ m = a * b) : a ^ n = a ∧ b ^ m = b := by
  have h1 : a⁻¹ * a ^ n = b * (b ^ m)⁻¹ := by
    calc a⁻¹ * a ^ n = a⁻¹ * (a ^ n * b ^ m) * (b ^ m)⁻¹ := by group
      _ = a⁻¹ * (a * b) * (b ^ m)⁻¹ := by rw [h]
      _ = b * (b ^ m)⁻¹ := by group
  have hc := hST _ (S.mul_mem (S.inv_mem ha) (S.pow_mem ha n))
    (h1 ▸ T.mul_mem hb (T.inv_mem (T.pow_mem hb m)))
  refine ⟨?_, ?_⟩
  · rw [inv_mul_eq_one] at hc
    exact hc.symm
  · rw [hc, eq_comm, mul_inv_eq_one] at h1
    exact h1.symm

end FrobeniusIsometryEigen

open FrobeniusIsometryEigen

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_eigen_normalizer (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {G : Subgroup (V ≃ₗ[K] V)}
    (hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hsq : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ 2 ∈ G)
    (hmul : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ∉ G → g' ∉ G → g * g' ∈ G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : ¬ p ∣ Fintype.card K ^ 2 - 1)
    (hq3 : ¬ p ∣ Fintype.card K ^ 3 - 1) {E : Subgroup (V ≃ₗ[K] V)} (hEG : E ≤ G)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hsc : ∀ c ∈ G, (∀ x ∈ E, c * x = x * c) → c ^ p = 1 → c ∈ E)
    (hcard : p ^ 2 ≤ Nat.card E) :
    ∃ y ∈ G, (∀ x ∈ E, y * x * y⁻¹ ∈ E) ∧ (∀ x ∈ E, y * x * y⁻¹ = x → x = 1) ∧
      (∃ x ∈ E, x ≠ 1 ∧ y * x * y⁻¹ = x ^ Fintype.card K) ∧
      ∀ x ∈ E, (y * x * y⁻¹) ^ Fintype.card K = x → x = 1 := by
  classical
  have := Fact.mk hp
  set q := Fintype.card K with hq_def
  have hpK : (p : K) ≠ 0 := by
    rw [FrobeniusIsometry.natCast_eq_one_of_odd (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  have hq1 : ¬ p ∣ q ^ 1 - 1 := fun h => hq2 (h.trans (by
    simpa only [pow_one, one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2))
  have hord : ∀ x ∈ E, ∀ m : ℕ, ¬ p ∣ m → x ^ m = 1 → x = 1 := by
    intro x hx m hm hxm
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hexp x hx)) with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ orderOf_dvd_of_pow_eq_one hxm) hm
  have hfixpow : ∀ x ∈ E, ∀ c : ℕ, ¬ p ∣ q ^ c - 1 → x ^ (q ^ c) = x → x = 1 := by
    intro x hx c hc hxc
    refine hord x hx (q ^ c - 1) hc ?_
    have h1 : 1 ≤ q ^ c := Nat.one_le_pow _ _ Fintype.card_pos
    calc x ^ (q ^ c - 1) = x ^ (q ^ c - 1 + 1) * x⁻¹ := by rw [pow_succ, mul_inv_cancel_right]
      _ = 1 := by rw [Nat.sub_add_cancel h1, hxc, mul_inv_cancel]
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V))
    fun f₁ f₂ h => LinearEquiv.ext (congrFun h)
  have : Finite E := Subtype.finite
  obtain ⟨⟨x₀, hx₀⟩, hx₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot E).mp
      (lt_of_lt_of_le (Nat.one_lt_pow two_ne_zero hp.one_lt) hcard))
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀1' (Subtype.ext h)
  have hordx : orderOf x₀ = p := orderOf_eq_prime (hexp x₀ hx₀) hx₀1
  obtain ⟨y₀, hy₀, hy₀n⟩ : ∃ y₀ ∈ E, y₀ ∉ Subgroup.zpowers x₀ := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (fun y hy => hcon y hy : E ≤ Subgroup.zpowers x₀)
    rw [Nat.card_zpowers, hordx] at h1
    have h2 := hcard.trans h1
    have h3 : p * 1 < p * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
    rw [sq] at h2
    omega
  have hy₀x : ∀ a : ℕ, x₀ ^ a * y₀ ≠ 1 := fun a h => hy₀n (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x₀) a))
  obtain ⟨z, hzE, hz1, w, hwE, v₀, hzv₀, hwv₀⟩ :=
    exists_ne_one_fixed_moved hp hpK hcomm hexp hx₀ hy₀ hx₀1 hy₀x
  let e : V →ₗ[K] V := (p : K)⁻¹ • avg p z
  have he_apply : ∀ v, e v = (p : K)⁻¹ • avg p z v := fun v => rfl
  have hze : ∀ v, z (e v) = e v := fun v => by
    rw [he_apply, map_smul, apply_avg (hexp z hzE)]
  have hefix : ∀ v, z v = v → e v = v := fun v hv => by
    rw [he_apply, avg_apply_of_fixed hv, ← Nat.cast_smul_eq_nsmul K, smul_smul,
      inv_mul_cancel₀ hpK, one_smul]
  have hee : ∀ v, e (e v) = e v := fun v => hefix _ (hze v)
  have hk : ∀ v, e (v - e v) = 0 := fun v => by rw [map_sub, hee, sub_self]
  have hxe : ∀ x ∈ E, ∀ v, x (e v) = e (x v) := fun x hx v => by
    rw [he_apply, he_apply, map_smul, avg_comm (hcomm x hx z hzE)]
  let B := QuadraticMap.polarBilin Q
  have hB : ∀ u v, B u v = QuadraticMap.polar Q u v := fun u v => rfl
  have hBsymm : ∀ u v, B u v = B v u := fun u v => QuadraticMap.polar_comm Q u v
  have hEO : ∀ x ∈ E, x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun x hx => hGO (hEG hx)
  have hBO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ u v, B (g u) (g v) = B u v :=
    fun g hg u v => by
      simp only [hB, QuadraticMap.polar,
        ← map_add, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg]
  have hperp : ∀ u v, e u = 0 → e v = v → B u v = 0 := by
    intro u v hu hv
    have hzv : z v = v := hv ▸ hze v
    have h1 : B (avg p z u) v = (p : K) * B u v := by
      rw [avg_apply, map_sum, LinearMap.sum_apply]
      have : ∀ i ∈ Finset.range p, B ((z ^ i) u) v = B u v := fun i _ => by
        conv_lhs => rw [← pow_apply_of_fixed hzv i]
        exact hBO _ (hEO _ (E.pow_mem hzE i)) u v
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : avg p z u = (p : K) • e u := by
      rw [he_apply, smul_smul, mul_inv_cancel₀ hpK, one_smul]
    rw [h2, hu, smul_zero, map_zero, LinearMap.zero_apply] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hpK
  have hker_of : ∀ u, (∀ v, e v = v → B u v = 0) → e u = 0 := by
    intro u hu
    refine hQ.1 (e u) fun t => ?_
    have h1 : B (e u) (e t) = 0 := by
      have h2 : B (u - e u) (e t) = 0 := hperp _ _ (by rw [map_sub, hee, sub_self]) (hee t)
      rwa [map_sub, LinearMap.sub_apply, hu _ (hee t), zero_sub, neg_eq_zero] at h2
    have h3 : B (e u) (t - e t) = 0 := by
      rw [hBsymm]
      exact hperp _ _ (by rw [map_sub, hee, sub_self]) (hee u)
    rw [map_sub, h1, sub_zero] at h3
    exact h3
  have hrange_of : ∀ v, (∀ u, e u = 0 → B u v = 0) → e v = v := by
    intro v hv
    have h0 : v - e v = 0 := by
      refine hQ.1 (v - e v) fun t => ?_
      have h1 : B (v - e v) (e t) = 0 := hperp _ _ (by rw [map_sub, hee, sub_self]) (hee t)
      have h2 : B (v - e v) (t - e t) = 0 := by
        have hk : e (t - e t) = 0 := by rw [map_sub, hee, sub_self]
        rw [LinearMap.map_sub₂, hBsymm v, hv _ hk, hBsymm (e v), hperp _ _ hk (hee v),
          sub_zero]
      calc B (v - e v) t = B (v - e v) (e t + (t - e t)) := by rw [add_sub_cancel]
        _ = 0 := by rw [map_add, h1, h2, add_zero]
    exact (sub_eq_zero.mp h0).symm
  let e' : V →ₗ[K] V := LinearMap.id - e
  have he'_apply : ∀ v, e' v = v - e v := fun v => rfl
  have hee' : ∀ v, e' (e' v) = e' v := fun v => by
    rw [he'_apply, he'_apply, map_sub, hee, sub_self, sub_zero]
  have hxe' : ∀ x ∈ E, ∀ v, x (e' v) = e' (x v) := fun x hx v => by
    rw [he'_apply, he'_apply, map_sub, hxe x hx]
  have hperpe : ∀ u w, e u = 0 → e w = w → QuadraticMap.polar Q u w = 0 := hperp
  have hperpe' : ∀ u w, e' u = 0 → e' w = w → QuadraticMap.polar Q u w = 0 := by
    intro u w hu hw
    rw [he'_apply, sub_eq_zero] at hu
    rw [he'_apply, sub_eq_self] at hw
    rw [← hB, hBsymm]
    exact hperp w u hw hu.symm
  have hpartE : ∀ (f : V →ₗ[K] V) (hf : ∀ v, f (f v) = f v)
      (hfx : ∀ x ∈ E, ∀ v, x (f v) = f (x v)),
      (∀ u w, f u = 0 → f w = w → QuadraticMap.polar Q u w = 0) →
      ∀ x (hx : x ∈ E), partEquiv f hf x (hfx x hx) ∈ E := by
    intro f hf hfx hfp x hx
    set P := partEquiv f hf x (hfx x hx)
    have hPO : P ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      partEquiv_mem_orthogonalGroup hf hfp (hfx x hx) (hEO x hx)
    have hPp : P ^ p = 1 := LinearEquiv.ext fun v => by
      rw [partEquiv_pow_apply, hexp x hx, one_apply', one_apply', sub_add_cancel]
    have hPG : P ∈ G := by
      obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
      have : P = (P ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = p + 1 by omega, pow_succ, hPp, one_mul]
      rw [this]
      exact G.pow_mem (hsq P hPO) _
    refine hsc P hPG (fun c hc => ?_) hPp
    exact (partEquiv_comm hf x (hfx x hx) (hcomm c hc x hx) (hfx c hc)).symm
  let EA : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {g | g ∈ E ∧ ∀ v, e v = v → g v = v}
      mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, fun v hv => by
        rw [LinearEquiv.mul_apply, hb.2 v hv, ha.2 v hv]⟩
      one_mem' := ⟨E.one_mem, fun v _ => rfl⟩
      inv_mem' := fun {a} ha => ⟨E.inv_mem ha.1, fun v hv => by
        change a.symm v = v
        rw [LinearEquiv.symm_apply_eq, ha.2 v hv]⟩ }
  let EB : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {g | g ∈ E ∧ ∀ v, e v = 0 → g v = v}
      mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, fun v hv => by
        rw [LinearEquiv.mul_apply, hb.2 v hv, ha.2 v hv]⟩
      one_mem' := ⟨E.one_mem, fun v _ => rfl⟩
      inv_mem' := fun {a} ha => ⟨E.inv_mem ha.1, fun v hv => by
        change a.symm v = v
        rw [LinearEquiv.symm_apply_eq, ha.2 v hv]⟩ }
  have hEA : ∀ g, g ∈ EA ↔ g ∈ E ∧ ∀ v, e v = v → g v = v := fun g => Iff.rfl
  have hEB : ∀ g, g ∈ EB ↔ g ∈ E ∧ ∀ v, e v = 0 → g v = v := fun g => Iff.rfl
  have hAB : ∀ c ∈ EA, c ∈ EB → c = 1 := fun c hcA hcB => LinearEquiv.ext fun v => by
    rw [one_apply', ← sub_add_cancel v (e v), map_add, hcA.2 _ (hee v),
      hcB.2 _ (by rw [map_sub, hee, sub_self])]
  have hdec : ∀ x ∈ E, ∃ xa ∈ EA, ∃ xb ∈ EB, x = xa * xb := by
    intro x hx
    refine ⟨partEquiv e hee x (hxe x hx), ⟨hpartE e hee hxe hperpe x hx, fun v hv => ?_⟩,
      partEquiv e' hee' x (hxe' x hx), ⟨hpartE e' hee' hxe' hperpe' x hx, fun v hv => ?_⟩,
      LinearEquiv.ext fun v => ?_⟩
    · rw [partEquiv_apply, hv, sub_self, map_zero, zero_add]
    · rw [partEquiv_apply, he'_apply, hv, sub_zero, sub_self, map_zero, zero_add]
    · have hX : partEquiv e' hee' x (hxe' x hx) v = x (e v) + (v - e v) := by
        rw [partEquiv_apply, he'_apply, sub_sub_cancel]
      have heX : e (x (e v) + (v - e v)) = x (e v) := by
        rw [map_add, ← hxe x hx (e v), hee, hk v, add_zero]
      rw [LinearEquiv.mul_apply, hX, partEquiv_apply, heX, add_sub_cancel_left, ← map_add,
        sub_add_cancel]
  have hpgrp : ∀ S : Subgroup (V ≃ₗ[K] V), S ≤ E → Odd (Nat.card S) := by
    intro S hSE
    have hS : IsPGroup p S := fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, hexp g (hSE g.2), Subgroup.coe_one])⟩
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hEAE : EA ≤ E := fun g hg => hg.1
  have hEBE : EB ≤ E := fun g hg => hg.1
  obtain ⟨gA, hgAO, hgA, hgAfix⟩ := exists_mem_orthogonalGroup_conj_eq_pow_card Q hQ (E := EA)
    (fun x hx y hy => hcomm x hx.1 y hy.1) (hpgrp EA hEAE) (fun g hg => hEO g hg.1)
  obtain ⟨gB, hgBO, hgB, hgBfix⟩ := exists_mem_orthogonalGroup_conj_eq_pow_card Q hQ (E := EB)
    (fun x hx y hy => hcomm x hx.1 y hy.1) (hpgrp EB hEBE) (fun g hg => hEO g hg.1)
  have hgAr : ∀ v, e v = v → gA v = v := fun v hv => hgAfix v fun x hx => hx.2 v hv
  have hgBk : ∀ v, e v = 0 → gB v = v := fun v hv => hgBfix v fun x hx => hx.2 v hv
  have hgAk : ∀ u, e u = 0 → e (gA u) = 0 := fun u hu => hker_of _ fun v hv => by
    rw [← hgAr v hv, hBO gA hgAO]
    exact hperp u v hu hv
  have hgBr : ∀ v, e v = v → e (gB v) = gB v := fun v hv => hrange_of _ fun u hu => by
    rw [← hgBk u hu, hBO gB hgBO]
    exact hperp u v hu hv
  have hcA : ∀ s ∈ EB, gA * s = s * gA := fun s hs => LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hs1 : e (s (e v)) = s (e v) := by rw [← hxe s hs.1, hee]
    calc gA (s v) = gA (s (e v) + (v - e v)) := by
          rw [← hs.2 _ (hk v), ← map_add, add_sub_cancel]
      _ = s (e v) + gA (v - e v) := by rw [map_add, hgAr _ hs1]
      _ = s (gA (e v) + gA (v - e v)) := by
          rw [map_add, hgAr _ (hee v), hs.2 _ (hgAk _ (hk v))]
      _ = s (gA v) := by rw [← map_add, add_sub_cancel]
  have hcB : ∀ s ∈ EA, gB * s = s * gB := fun s hs => LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hs1 : e (s (v - e v)) = 0 := by rw [← hxe s hs.1, hk, map_zero]
    have hsv : s v = e v + s (v - e v) := by
      conv_lhs => rw [← add_sub_cancel (e v) v]
      rw [map_add, hs.2 _ (hee v)]
    calc gB (s v) = gB (e v + s (v - e v)) := by rw [hsv]
      _ = gB (e v) + s (v - e v) := by rw [map_add, hgBk _ hs1]
      _ = s (gB (e v) + gB (v - e v)) := by
          rw [map_add, hs.2 _ (hgBr _ (hee v)), hgBk _ (hk v)]
      _ = s (gB v) := by rw [← map_add, add_sub_cancel]
  have hconjA := conj_pow_eq_pow_pow (S := EA) hgA
  have hconjB := conj_pow_eq_pow_pow (S := EB) hgB
  have hact : ∀ a b : ℕ, ∀ xa ∈ EA, ∀ xb ∈ EB,
      (gA ^ a * gB ^ b) * (xa * xb) * (gA ^ a * gB ^ b)⁻¹ = xa ^ (q ^ a) * xb ^ (q ^ b) := by
    intro a b xa hxa xb hxb
    have h1 : gB ^ b * (xa * xb) * (gB ^ b)⁻¹ = xa * xb ^ (q ^ b) := by
      calc gB ^ b * (xa * xb) * (gB ^ b)⁻¹ = (gB ^ b * xa) * xb * (gB ^ b)⁻¹ := by
            simp only [mul_assoc]
        _ = (xa * gB ^ b) * xb * (gB ^ b)⁻¹ := by
            rw [(Commute.pow_left (hcB xa hxa : Commute gB xa) b).eq]
        _ = xa * (gB ^ b * xb * (gB ^ b)⁻¹) := by simp only [mul_assoc]
        _ = xa * xb ^ (q ^ b) := by rw [hconjB b xb hxb]
    have hxb' : xb ^ (q ^ b) ∈ EB := EB.pow_mem hxb _
    calc (gA ^ a * gB ^ b) * (xa * xb) * (gA ^ a * gB ^ b)⁻¹
        = gA ^ a * (gB ^ b * (xa * xb) * (gB ^ b)⁻¹) * (gA ^ a)⁻¹ := by
          rw [mul_inv_rev]
          simp only [mul_assoc]
      _ = gA ^ a * (xa * xb ^ (q ^ b)) * (gA ^ a)⁻¹ := by rw [h1]
      _ = (gA ^ a * xa * (gA ^ a)⁻¹) * (gA ^ a * xb ^ (q ^ b) * (gA ^ a)⁻¹) := by
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = xa ^ (q ^ a) * xb ^ (q ^ b) := by
          rw [hconjA a xa hxa, (Commute.pow_left (hcA _ hxb' : Commute gA _) a).eq, mul_assoc,
            mul_inv_cancel, mul_one]
  have hfinish : ∀ a b : ℕ, gA ^ a * gB ^ b ∈ G → ¬ p ∣ q ^ a - 1 → ¬ p ∣ q ^ b - 1 →
      ¬ p ∣ q ^ (a + 1) - 1 → ¬ p ∣ q ^ (b + 1) - 1 →
      (∃ x ∈ E, x ≠ 1 ∧ (gA ^ a * gB ^ b) * x * (gA ^ a * gB ^ b)⁻¹ = x ^ q) →
      ∃ y ∈ G, (∀ x ∈ E, y * x * y⁻¹ ∈ E) ∧ (∀ x ∈ E, y * x * y⁻¹ = x → x = 1) ∧
        (∃ x ∈ E, x ≠ 1 ∧ y * x * y⁻¹ = x ^ q) ∧
        ∀ x ∈ E, (y * x * y⁻¹) ^ q = x → x = 1 := by
    intro a b hyG ha hb ha1 hb1 hev
    refine ⟨_, hyG, fun x hx => ?_, fun x hx hxy => ?_, hev, fun x hx hxy => ?_⟩
    · obtain ⟨xa, hxa, xb, hxb, rfl⟩ := hdec x hx
      rw [hact a b xa hxa xb hxb]
      exact E.mul_mem (E.pow_mem hxa.1 _) (E.pow_mem hxb.1 _)
    · obtain ⟨xa, hxa, xb, hxb, rfl⟩ := hdec x hx
      rw [hact a b xa hxa xb hxb] at hxy
      obtain ⟨h1, h2⟩ := pow_eq_self_of_mul hAB hxa hxb hxy
      rw [hfixpow xa hxa.1 a ha h1, hfixpow xb hxb.1 b hb h2, one_mul]
    · obtain ⟨xa, hxa, xb, hxb, rfl⟩ := hdec x hx
      rw [hact a b xa hxa xb hxb, (Commute.mul_pow (hcomm _ (E.pow_mem hxa.1 _) _
        (E.pow_mem hxb.1 _)) q), ← pow_mul, ← pow_mul, ← pow_succ, ← pow_succ] at hxy
      obtain ⟨h1, h2⟩ := pow_eq_self_of_mul hAB hxa hxb hxy
      rw [hfixpow xa hxa.1 _ ha1 h1, hfixpow xb hxb.1 _ hb1 h2, one_mul]
  have hzA : z ∈ EA := ⟨hzE, fun v hv => (hv ▸ hze v)⟩
  have hq2' : ¬ p ∣ q ^ 2 - 1 := hq2
  have hq3' : ¬ p ∣ q ^ 3 - 1 := hq3
  have hevz : ∀ a b : ℕ, (gA ^ a * gB ^ b) * z * (gA ^ a * gB ^ b)⁻¹ = z ^ (q ^ a) := by
    intro a b
    have h := hact a b z hzA 1 EB.one_mem
    rwa [mul_one, one_pow, mul_one] at h
  by_cases hA : gA ∈ G
  · refine hfinish 1 2 (by rw [pow_one]; exact G.mul_mem hA (hsq gB hgBO)) hq1 hq2' hq2' hq3'
      ⟨z, hzE, hz1, by rw [hevz, pow_one]⟩
  by_cases hB' : gB ∈ G
  · let w' := partEquiv e' hee' w (hxe' w hwE)
    have hw'B : w' ∈ EB := ⟨hpartE e' hee' hxe' hperpe' w hwE, fun v hv => by
      change w (v - e' v) + e' v = v
      rw [he'_apply, hv, sub_zero, sub_self, map_zero, zero_add]⟩
    have hw'1 : w' ≠ 1 := fun h1 => hwv₀ (by
      have h := congrArg (fun f : V ≃ₗ[K] V => f v₀) h1
      change w (v₀ - e' v₀) + e' v₀ = v₀ at h
      rwa [he'_apply, hefix v₀ hzv₀, sub_self, sub_zero, add_zero] at h)
    refine hfinish 2 1 (by rw [pow_one]; exact G.mul_mem (hsq gA hgAO) hB') hq2' hq1 hq3' hq2'
      ⟨w', hw'B.1, hw'1, ?_⟩
    have h := hact 2 1 1 EA.one_mem w' hw'B
    rw [one_mul, one_pow, one_mul] at h
    rw [h, pow_one]
  · refine hfinish 1 1 (by rw [pow_one, pow_one]; exact hmul gA hgAO gB hgBO hA hB') hq1 hq1
      hq2' hq2' ⟨z, hzE, hz1, by rw [hevz, pow_one]⟩

end CFSG.LinearAlgebra
