module

public import CFSG.LieType.TorusWeights.Basic
public import CFSG.RepresentationTheory.SL2NatSum.ChooseTwo

public section

namespace CFSG.LieType.TorusWeights

open Finset
open Nat

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {n : ℕ} {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {X : Type*} [AddCommGroup X] [Module K X]
  (h : (Fin n → Kˣ) →* G) (ρ : Representation K G X) (x : K → G)

@[expose] noncomputable def rootCoeff (k : ℕ) (d : K) : K :=
  if k = 0 then (if d = 0 then 1 else 0)
  else if k < Nat.card Kˣ then (if d = 0 then 0 else (d ^ k)⁻¹)
  else if k = Nat.card Kˣ then 1 else 0

@[expose] noncomputable def rootOp (k : ℕ) : Module.End K X :=
  ∑ d : K, rootCoeff k d • ρ (x d)

omit [CharP K 2] in
theorem rootOp_apply (k : ℕ) (v : X) :
    rootOp ρ x k v = ∑ d : K, rootCoeff k d • ρ (x d) v := by
  rw [rootOp]
  exact LinearMap.sum_apply _ _ v

omit [Finite K] [CharP K 2] in
theorem rootCoeff_zero (d : K) : rootCoeff 0 d = if d = 0 then 1 else 0 := by
  simp [rootCoeff]

omit [Finite K] [CharP K 2] in
theorem rootCoeff_of_pos_of_lt {k : ℕ} (hk0 : 0 < k) (hkN : k < Nat.card Kˣ) (d : K) :
    rootCoeff k d = if d = 0 then 0 else (d ^ k)⁻¹ := by
  rw [rootCoeff, if_neg hk0.ne', if_pos hkN]

omit [CharP K 2] in
theorem rootCoeff_card (d : K) : rootCoeff (Nat.card Kˣ) d = 1 := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  rw [rootCoeff, if_neg hN, if_neg (lt_irrefl (Nat.card Kˣ)), if_pos rfl]

omit [CharP K 2] in
theorem rootCoeff_of_lt {k : ℕ} (hk : Nat.card Kˣ < k) (d : K) : rootCoeff k d = 0 := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  have hk0 : k ≠ 0 := by omega
  have hnk : ¬ k < Nat.card Kˣ := by omega
  have hne : k ≠ Nat.card Kˣ := by omega
  rw [rootCoeff, if_neg hk0, if_neg hnk, if_neg hne]

omit [CharP K 2] in
private theorem sum_K_eq_zero_add {M : Type*} [AddCommMonoid M] (f : K → M) :
    (∑ d : K, f d) = f 0 + ∑ u : Kˣ, f (u : K) := by
  classical
  rw [← Finset.add_sum_erase (Finset.univ : Finset K) f (Finset.mem_univ 0)]
  congr 1
  refine Finset.sum_bij (fun d hd => Units.mk0 d (Finset.ne_of_mem_erase hd)) ?_ ?_ ?_ ?_
  · intro d _
    exact Finset.mem_univ _
  · intro d₁ h₁ d₂ h₂ hd
    simpa using congrArg Units.val hd
  · intro u _
    exact ⟨(u : K), Finset.mem_erase.mpr ⟨u.ne_zero, Finset.mem_univ _⟩, Units.ext rfl⟩
  · intro d _
    rfl

private theorem sum_units_zpow (n : ℤ) :
    (∑ u : Kˣ, (u : K) ^ n) = if (Nat.card Kˣ : ℤ) ∣ n then 1 else 0 := by
  rcases le_or_gt 0 n with hn | hn
  · have hn' : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn).symm
    rw [hn']
    simp only [zpow_natCast, sum_units_pow, Int.natCast_dvd_natCast]
  · have hm : 0 ≤ -n := by omega
    set m : ℕ := (-n).toNat with hmdef
    have hn' : n = -(m : ℤ) := by
      rw [hmdef, Int.toNat_of_nonneg hm]
      omega
    have h1 : (∑ u : Kˣ, (u : K) ^ n) = ∑ u : Kˣ, (u : K) ^ m := by
      rw [hn']
      simp only [zpow_neg, zpow_natCast]
      refine Fintype.sum_bijective (fun u : Kˣ => u⁻¹)
        ⟨fun a b h => ?_, fun b => ⟨b⁻¹, by simp⟩⟩
        (fun u : Kˣ => ((u : K) ^ m)⁻¹) (fun u : Kˣ => (u : K) ^ m) fun u => ?_
      · simpa using congrArg Inv.inv h
      · rw [Units.val_inv_eq_inv_val, inv_pow]
    have hiff : ((Nat.card Kˣ : ℤ) ∣ n) ↔ Nat.card Kˣ ∣ m := by
      rw [hn', Int.dvd_neg, Int.natCast_dvd_natCast]
    rw [h1, sum_units_pow]
    by_cases h : Nat.card Kˣ ∣ m
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]

omit [CharP K 2] in
private theorem rootCoeff_sum_mul_zero {m : ℕ} (hm : m ≤ Nat.card Kˣ) :
    (∑ d : K, rootCoeff 0 d * d ^ m) = if 0 = m then 1 else 0 := by
  rw [Finset.sum_eq_single (0 : K)]
  · rw [rootCoeff_zero, if_pos rfl, one_mul]
    by_cases hm0 : m = 0
    · subst hm0
      simp
    · rw [zero_pow hm0, if_neg (Ne.symm hm0)]
  · intro d _ hd
    rw [rootCoeff_zero, if_neg hd, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (0 : K)) h

private theorem rootCoeff_sum_mul_card {m : ℕ} (hm : m ≤ Nat.card Kˣ) :
    (∑ d : K, rootCoeff (Nat.card Kˣ) d * d ^ m) =
      if Nat.card Kˣ = m then 1 else 0 := by
  rw [sum_K_eq_zero_add]
  have h0 : rootCoeff (Nat.card Kˣ) (0 : K) * (0 : K) ^ m = if m = 0 then 1 else 0 := by
    rw [rootCoeff_card, one_mul]
    by_cases hm0 : m = 0
    · subst hm0
      simp
    · rw [zero_pow hm0, if_neg hm0]
  rw [h0]
  have h1 : ∀ u : Kˣ, rootCoeff (Nat.card Kˣ) (u : K) * (u : K) ^ m = (u : K) ^ m := by
    intro u
    rw [rootCoeff_card, one_mul]
  simp only [h1]
  rw [sum_units_pow]
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  by_cases hm0 : m = 0
  · subst hm0
    rw [if_pos rfl, if_pos (dvd_zero _), if_neg hN]
    exact CharTwo.add_self_eq_zero 1
  · have hdvd : Nat.card Kˣ ∣ m ↔ m = Nat.card Kˣ := by
      constructor
      · intro hd
        exact Nat.le_antisymm hm (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd)
      · intro h
        rw [h]
    rw [if_neg hm0]
    by_cases h : Nat.card Kˣ ∣ m
    · rw [if_pos h, if_pos (hdvd.mp h).symm, zero_add]
    · rw [if_neg h, if_neg (fun hnm => h (hdvd.mpr hnm.symm)), zero_add]

private theorem rootCoeff_sum_mul_pos {k m : ℕ} (hk0 : 0 < k) (hkN : k < Nat.card Kˣ)
    (hm : m ≤ Nat.card Kˣ) :
    (∑ d : K, rootCoeff k d * d ^ m) = if k = m then 1 else 0 := by
  rw [sum_K_eq_zero_add]
  have h0 : rootCoeff k (0 : K) * (0 : K) ^ m = 0 := by
    rw [rootCoeff_of_pos_of_lt hk0 hkN, if_pos rfl, zero_mul]
  rw [h0, zero_add]
  have hterm : ∀ u : Kˣ, rootCoeff k (u : K) * (u : K) ^ m =
      ((u ^ ((m : ℤ) - k) : Kˣ) : K) := by
    intro u
    rw [rootCoeff_of_pos_of_lt hk0 hkN, if_neg (by exact u.ne_zero)]
    rw [Units.val_zpow_eq_zpow_val, zpow_sub₀ (by exact u.ne_zero), div_eq_mul_inv,
      mul_comm]
    simp only [zpow_natCast]
  rw [Finset.sum_congr rfl fun u _ => hterm u]
  simp only [Units.val_zpow_eq_zpow_val]
  rw [sum_units_zpow]
  have hiff : ((Nat.card Kˣ : ℤ) ∣ ((m : ℤ) - k)) ↔ k = m := by
    by_cases hkm : k ≤ m
    · have h1 : (m : ℤ) - k = ((m - k : ℕ) : ℤ) := by omega
      rw [h1, Int.natCast_dvd_natCast]
      constructor
      · intro hd
        rcases Nat.eq_zero_or_pos (m - k) with h2 | h2
        · omega
        · exact absurd (Nat.le_of_dvd h2 hd) (by omega)
      · intro h
        subst h
        simp
    · have hkm' : m < k := by omega
      have h1 : (m : ℤ) - k = -((k - m : ℕ) : ℤ) := by omega
      rw [h1, Int.dvd_neg, Int.natCast_dvd_natCast]
      constructor
      · intro hd
        exact absurd (Nat.le_of_dvd (by omega : 0 < k - m) hd) (by omega)
      · intro h
        omega
  by_cases hkm : k = m
  · rw [if_pos (hiff.mpr hkm), if_pos hkm]
  · rw [if_neg (fun h => hkm (hiff.mp h)), if_neg hkm]

theorem rootCoeff_sum_mul {k m : ℕ} (hk : k ≤ Nat.card Kˣ) (hm : m ≤ Nat.card Kˣ) :
    (∑ d : K, rootCoeff k d * d ^ m) = if k = m then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact rootCoeff_sum_mul_zero hm
  · rcases eq_or_lt_of_le hk with hk' | hk'
    · obtain rfl : k = Nat.card Kˣ := hk'
      exact rootCoeff_sum_mul_card hm
    · exact rootCoeff_sum_mul_pos hkpos hk' hm

private theorem sum_range_pow_succ (u : K) :
    (∑ k ∈ Finset.range (Nat.card Kˣ), u ^ (k + 1)) = if u = 1 then 1 else 0 := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  by_cases hu : u = 0
  · rw [if_neg (by rw [hu]; exact zero_ne_one), hu]
    simp
  · have huN : u ^ Nat.card Kˣ = 1 := by
      have h := congrArg ((↑) : Kˣ → K) (pow_card_eq_one' (x := Units.mk0 u hu))
      rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h
    have hgeom : (∑ k ∈ Finset.range (Nat.card Kˣ), u ^ k) * (u - 1) = 0 := by
      rw [geom_sum_mul, huN, sub_self]
    rw [show (∑ k ∈ Finset.range (Nat.card Kˣ), u ^ (k + 1)) =
        u * ∑ k ∈ Finset.range (Nat.card Kˣ), u ^ k from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [pow_succ, mul_comm]]
    by_cases hu1 : u = 1
    · subst hu1
      rw [if_pos rfl, one_mul]
      rw [Finset.sum_congr rfl fun k _ => one_pow k, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
      exact natCard_units_cast_eq_one
    · rw [if_neg hu1]
      rcases mul_eq_zero.mp hgeom with h | h
      · rw [h, mul_zero]
      · exact absurd (sub_eq_zero.mp h) hu1

omit [CharP K 2] in
private theorem sum_range_rootCoeff_zero (c : K) :
    (∑ k ∈ Finset.range (Nat.card Kˣ),
      c ^ (k + 1) * rootCoeff (k + 1) (0 : K)) = c ^ Nat.card Kˣ := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  conv_lhs => rw [show Nat.card Kˣ = (Nat.card Kˣ - 1) + 1 from
    (Nat.sub_one_add_one hN).symm]
  rw [Finset.sum_range_succ]
  have hlast : c ^ (Nat.card Kˣ - 1 + 1) * rootCoeff (Nat.card Kˣ - 1 + 1) (0 : K) =
      c ^ Nat.card Kˣ := by
    rw [Nat.sub_one_add_one hN, rootCoeff_card, mul_one]
  rw [hlast]
  have hzero : (∑ k ∈ Finset.range (Nat.card Kˣ - 1),
      c ^ (k + 1) * rootCoeff (k + 1) (0 : K)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [rootCoeff_of_pos_of_lt (Nat.succ_pos k) (by
      have := Finset.mem_range.mp hk
      omega), if_pos rfl, mul_zero]
  rw [hzero, zero_add]

private theorem rootOp_interpolation_zero (c : K) :
    (∑ j ∈ Finset.range (Nat.card Kˣ + 1), c ^ j * rootCoeff j (0 : K)) =
      if c = 0 then 1 else 0 := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  rw [Finset.sum_range_succ']
  have h0 : c ^ 0 * rootCoeff 0 (0 : K) = 1 := by
    rw [rootCoeff_zero, if_pos rfl, mul_one, pow_zero]
  rw [sum_range_rootCoeff_zero, h0]
  by_cases hc : c = 0
  · subst hc
    rw [zero_pow hN, zero_add, if_pos rfl]
  · rw [if_neg hc]
    have hcN : c ^ Nat.card Kˣ = 1 := by
      have h := congrArg ((↑) : Kˣ → K) (pow_card_eq_one' (x := Units.mk0 c hc))
      rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h
    rw [hcN]
    exact CharTwo.add_self_eq_zero 1

omit [CharP K 2] in
private theorem rootCoeff_pow_of_ne_zero {c d : K} (hd : d ≠ 0) {j : ℕ}
    (hj1 : 1 ≤ j) (hjN : j ≤ Nat.card Kˣ) :
    c ^ j * rootCoeff j d = (c * d⁻¹) ^ j := by
  rcases eq_or_lt_of_le hjN with hj | hj
  · rw [hj, rootCoeff_card, mul_one, mul_pow, inv_pow,
      show d ^ Nat.card Kˣ = 1 from by
        have h := congrArg ((↑) : Kˣ → K) (pow_card_eq_one' (x := Units.mk0 d hd))
        rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h,
      inv_one, mul_one]
  · rw [rootCoeff_of_pos_of_lt (by omega) hj, if_neg hd, ← inv_pow, ← mul_pow]

private theorem rootOp_interpolation_ne_zero {c d : K} (hd : d ≠ 0) :
    (∑ j ∈ Finset.range (Nat.card Kˣ + 1), c ^ j * rootCoeff j d) =
      if c = d then 1 else 0 := by
  have huval : c * d⁻¹ = 1 ↔ c = d := by
    constructor
    · intro h
      calc c = c * d⁻¹ * d := by rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
        _ = 1 * d := by rw [h]
        _ = d := one_mul d
    · intro h
      rw [h, mul_inv_cancel₀ hd]
  have hsum : (∑ j ∈ Finset.range (Nat.card Kˣ + 1), c ^ j * rootCoeff j d) =
      ∑ k ∈ Finset.range (Nat.card Kˣ), (c * d⁻¹) ^ (k + 1) := by
    rw [Finset.sum_range_succ']
    have h0 : c ^ 0 * rootCoeff 0 d = 0 := by
      rw [rootCoeff_zero, if_neg hd, mul_zero]
    rw [h0]
    simp only [add_zero]
    exact Finset.sum_congr rfl fun k hk =>
      rootCoeff_pow_of_ne_zero hd (Nat.succ_pos k)
        (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  rw [hsum, sum_range_pow_succ]
  by_cases hcd : c = d
  · rw [if_pos hcd, if_pos (huval.mpr hcd)]
  · rw [if_neg hcd, if_neg (fun h => hcd (huval.mp h))]

theorem rootOp_interpolation (c d : K) :
    (∑ j ∈ Finset.range (Nat.card Kˣ + 1), c ^ j * rootCoeff j d) =
      if c = d then 1 else 0 := by
  by_cases hd : d = 0
  · subst hd
    exact rootOp_interpolation_zero c
  · exact rootOp_interpolation_ne_zero hd

theorem rho_eq_sum (c : K) :
    ρ (x c) = ∑ k ∈ Finset.range (Nat.card Kˣ + 1), c ^ k • rootOp ρ x k := by
  ext v
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, rootOp_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ d : K, (∑ k ∈ Finset.range (Nat.card Kˣ + 1),
      c ^ k • (rootCoeff k d • ρ (x d) v)) =
      (if c = d then (1 : K) else 0) • ρ (x d) v := by
    intro d
    rw [show (∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        c ^ k • (rootCoeff k d • ρ (x d) v)) =
        ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
          (c ^ k * rootCoeff k d) • ρ (x d) v from
      Finset.sum_congr rfl fun k _ => (mul_smul _ _ _).symm]
    have h := rootOp_interpolation (K := K) c d
    rw [← Finset.sum_smul]
    exact congrArg (fun z : K => z • ρ (x d) v) h
  simp only [hinner]
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl, one_smul]
  · intro d _ hd
    rw [if_neg (Ne.symm hd), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ c) h

omit [CharP K 2] in
theorem rootOp_zero (hx0 : x 0 = 1) : rootOp ρ x 0 = 1 := by
  ext v
  rw [rootOp_apply, Finset.sum_eq_single (0 : K)]
  · rw [rootCoeff_zero, if_pos rfl, one_smul, hx0, map_one, Module.End.one_apply]
  · intro d _ hd
    rw [rootCoeff_zero, if_neg hd, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ (0 : K)) h

omit [CharP K 2] in
theorem rootOp_of_lt {k : ℕ} (hk : Nat.card Kˣ < k) : rootOp ρ x k = 0 := by
  ext v
  rw [rootOp_apply]
  simp only [rootCoeff_of_lt hk, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]

omit [CharP K 2] in
theorem rootCoeff_inv_mul (k : ℕ) {lam : K} (hlam : lam ≠ 0) (d : K) :
    rootCoeff k (lam⁻¹ * d) = lam ^ k * rootCoeff k d := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [rootCoeff_zero, rootCoeff_zero, pow_zero, one_mul]
    by_cases hd : d = 0
    · rw [hd, mul_zero, if_pos rfl]
    · rw [if_neg hd, if_neg (mul_ne_zero (inv_ne_zero hlam) hd)]
  · rcases lt_or_ge k (Nat.card Kˣ) with hkN | hkN
    · rw [rootCoeff_of_pos_of_lt hkpos hkN, rootCoeff_of_pos_of_lt hkpos hkN]
      by_cases hd : d = 0
      · rw [hd, mul_zero, if_pos rfl, mul_zero]
      · rw [if_neg (mul_ne_zero (inv_ne_zero hlam) hd), if_neg hd, mul_pow, mul_inv_rev,
          inv_pow, inv_inv, mul_comm]
    · rcases eq_or_lt_of_le hkN with hk | hk
      · rw [← hk, rootCoeff_card, rootCoeff_card,
          show lam ^ Nat.card Kˣ = 1 from by
            have h := congrArg ((↑) : Kˣ → K) (pow_card_eq_one' (x := Units.mk0 lam hlam))
            rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h,
          one_mul]
      · rw [rootCoeff_of_lt hk, rootCoeff_of_lt hk, mul_zero]

omit [CharP K 2] in
theorem rootOp_conj {α : Fin n → ZMod (Nat.card Kˣ)}
    (hconj : ∀ t c, h t * x c * (h t)⁻¹ = x ((wtChar α t : K) * c))
    (t : Fin n → Kˣ) (k : ℕ) :
    ρ (h t) * rootOp ρ x k =
      (wtChar α t : K) ^ k • (rootOp ρ x k * ρ (h t)) := by
  set lam : K := (wtChar α t : K) with hlamdef
  have hlam : lam ≠ 0 := by
    rw [hlamdef]
    exact_mod_cast (wtChar α t).ne_zero
  ext v
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, rootOp_apply,
    rootOp_apply, map_sum]
  have hterm : ∀ d : K, ρ (h t) (rootCoeff k d • ρ (x d) v) =
      rootCoeff k d • ρ (x (lam * d)) (ρ (h t) v) := by
    intro d
    rw [map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply]
    rw [show ρ (h t) * ρ (x d) = ρ (x (lam * d)) * ρ (h t) from by
      rw [← map_mul, ← map_mul]
      congr 1
      have hc := hconj t d
      calc h t * x d = h t * x d * (h t)⁻¹ * h t := by group
        _ = x (lam * d) * h t := by rw [hc]]
  rw [Finset.sum_congr rfl fun d _ => hterm d]
  have hreindex : (∑ d : K, rootCoeff k d • ρ (x (lam * d)) (ρ (h t) v)) =
      ∑ d : K, rootCoeff k (lam⁻¹ * d) • ρ (x d) (ρ (h t) v) := by
    refine Fintype.sum_bijective (fun d : K => lam * d) ⟨?_, ?_⟩ _ _ ?_
    · intro a b hab
      exact mul_left_cancel₀ hlam hab
    · intro b
      exact ⟨lam⁻¹ * b, by
        show lam * (lam⁻¹ * b) = b
        rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]⟩
    · intro d
      congr 2
      show d = lam⁻¹ * (lam * d)
      rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  rw [hreindex]
  have hhom : ∀ d : K, rootCoeff k (lam⁻¹ * d) • ρ (x d) (ρ (h t) v) =
      lam ^ k • (rootCoeff k d • ρ (x d) (ρ (h t) v)) := by
    intro d
    rw [rootCoeff_inv_mul k hlam, mul_smul]
  simp only [hhom, Finset.smul_sum]

omit [CharP K 2] in
theorem rootOp_mem_wtSpace {α : Fin n → ZMod (Nat.card Kˣ)}
    (hconj : ∀ t c, h t * x c * (h t)⁻¹ = x ((wtChar α t : K) * c))
    {a : Fin n → ZMod (Nat.card Kˣ)} {v : X} (hv : v ∈ wtSpace h ρ a) (k : ℕ) :
    rootOp ρ x k v ∈ wtSpace h ρ (a + (k : ZMod (Nat.card Kˣ)) • α) := by
  rw [mem_wtSpace] at hv ⊢
  intro t
  have h := congrArg (fun f : Module.End K X => f v) (rootOp_conj h ρ x hconj t k)
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [h, hv t, map_smul, smul_smul, wtChar_add, wtChar_natCast_smul, Units.val_mul,
    Units.val_pow_eq_pow_val, mul_comm]

omit [CharP K 2] in
theorem rootOp_conj_elt {g : G} {x x' : K → G}
    (hg : ∀ c, g * x c * g⁻¹ = x' c) (k : ℕ) :
    rootOp ρ x' k = ρ g * rootOp ρ x k * ρ g⁻¹ := by
  ext v
  simp only [rootOp_apply, Module.End.mul_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul]
  congr 1
  have hc : ρ (x' c) = ρ g * ρ (x c) * ρ g⁻¹ := by
    rw [← hg c, map_mul, map_mul]
  rw [hc, Module.End.mul_apply, Module.End.mul_apply]

omit [CharP K 2] in
theorem commute_rootOp {T : Module.End K X} (hT : ∀ c, Commute (ρ (x c)) T) (k : ℕ) :
    Commute (rootOp ρ x k) T := by
  rw [Commute]
  ext v
  simp only [rootOp_apply, Module.End.mul_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul]
  congr 1
  simp only [← Module.End.mul_apply]
  rw [(hT c).eq]

private theorem rootCoeff_sum_mul' {i r : ℕ} (hr : r ≤ Nat.card Kˣ) :
    (∑ c : K, rootCoeff i c * c ^ r) = if i = r then 1 else 0 := by
  by_cases hi : i ≤ Nat.card Kˣ
  · exact rootCoeff_sum_mul hi hr
  · have hir : i ≠ r := by omega
    rw [if_neg hir]
    exact Finset.sum_eq_zero fun c _ => by rw [rootCoeff_of_lt (by omega), zero_mul]

omit [CharP K 2] in
private theorem rootCoeff_mul_binomial_expand {i j k : ℕ} :
    (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) =
      ∑ r ∈ Finset.range (k + 1), (k.choose r : K) *
        (∑ c : K, rootCoeff i c * c ^ r) *
        (∑ d : K, rootCoeff j d * d ^ (k - r)) := by
  calc (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k)
      = ∑ c : K, ∑ d : K, ∑ r ∈ Finset.range (k + 1),
          (rootCoeff i c * c ^ r) * (rootCoeff j d * d ^ (k - r)) *
            (k.choose r : K) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = ∑ r ∈ Finset.range (k + 1), ∑ c : K, ∑ d : K,
          (rootCoeff i c * c ^ r) * (rootCoeff j d * d ^ (k - r)) *
            (k.choose r : K) := by
        rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.range (k + 1), (k.choose r : K) *
          (∑ c : K, rootCoeff i c * c ^ r) *
          (∑ d : K, rootCoeff j d * d ^ (k - r)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring

private theorem rootCoeff_mul_binomial_sum {i j k : ℕ} (hk : k ≤ Nat.card Kˣ) :
    (∑ r ∈ Finset.range (k + 1), (k.choose r : K) *
        (∑ c : K, rootCoeff i c * c ^ r) *
        (∑ d : K, rootCoeff j d * d ^ (k - r))) =
      if k = i + j then ((k.choose i : ℕ) : K) else 0 := by
  have hsum : ∀ r ∈ Finset.range (k + 1),
      (k.choose r : K) * (∑ c : K, rootCoeff i c * c ^ r) *
          (∑ d : K, rootCoeff j d * d ^ (k - r)) =
      (k.choose r : K) * (if i = r then 1 else 0) * (if j = k - r then 1 else 0) := by
    intro r hr
    have hrk : r ≤ k := by
      have := Finset.mem_range.mp hr
      omega
    rw [rootCoeff_sum_mul' (by omega : r ≤ Nat.card Kˣ),
      rootCoeff_sum_mul' (by omega : k - r ≤ Nat.card Kˣ)]
  rw [Finset.sum_congr rfl hsum]
  by_cases h : k = i + j
  · rw [if_pos h]
    have hi : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, if_pos (by omega : j = k - i)]
      ring
    · intro r _ hr
      rw [if_neg (fun hri : i = r => hr hri.symm)]
      ring
    · intro hnot
      exact absurd hi hnot
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun r hr => ?_
    by_cases hri : i = r
    · have hrk : r ≤ k := by
        have := Finset.mem_range.mp hr
        omega
      rw [if_pos hri]
      rw [if_neg (fun hjk : j = k - r => h (by omega))]
      ring
    · rw [if_neg hri]
      ring

private theorem rootCoeff_mul_binomial {i j k : ℕ} (hk : k ≤ Nat.card Kˣ) :
    (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) =
      if k = i + j then ((k.choose i : ℕ) : K) else 0 :=
  (rootCoeff_mul_binomial_expand).trans (rootCoeff_mul_binomial_sum hk)

omit [CharP K 2] in
private theorem rootOp_mul_expand (hadd : ∀ c d, x (c + d) = x c * x d) (i j : ℕ) (v : X) :
    (rootOp ρ x i * rootOp ρ x j) v =
      ∑ c : K, ∑ d : K,
        (rootCoeff i c * rootCoeff j d) • ρ (x (c + d)) v := by
  rw [Module.End.mul_apply]
  simp only [rootOp_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, ← hadd c d]

private theorem rootOp_mul_expand' (i j : ℕ) (v : X) :
    (∑ c : K, ∑ d : K, (rootCoeff i c * rootCoeff j d) • ρ (x (c + d)) v) =
      ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
          rootOp ρ x k v := by
  have hpoint : ∀ c : K, ρ (x c) v =
      ∑ k ∈ Finset.range (Nat.card Kˣ + 1), c ^ k • rootOp ρ x k v := by
    intro c
    rw [rho_eq_sum ρ x c]
    exact LinearMap.sum_apply _ _ v
  simp only [hpoint, Finset.smul_sum]
  calc (∑ c : K, ∑ d : K, ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        (rootCoeff i c * rootCoeff j d) • ((c + d) ^ k • rootOp ρ x k v))
      = ∑ k ∈ Finset.range (Nat.card Kˣ + 1), ∑ c : K, ∑ d : K,
          (rootCoeff i c * rootCoeff j d) • ((c + d) ^ k • rootOp ρ x k v) := by
        rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
          (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
            rootOp ρ x k v := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show (∑ c : K, ∑ d : K,
            (rootCoeff i c * rootCoeff j d) • ((c + d) ^ k • rootOp ρ x k v)) =
            ∑ c : K, (∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
              rootOp ρ x k v from by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [show (∑ d : K, (rootCoeff i c * rootCoeff j d) •
              ((c + d) ^ k • rootOp ρ x k v)) =
              ∑ d : K, (rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
                rootOp ρ x k v from
            Finset.sum_congr rfl fun d _ => smul_smul _ _ _]
          rw [← Finset.sum_smul]]
        rw [← Finset.sum_smul]

private theorem rootOp_mul_apply (hadd : ∀ c d, x (c + d) = x c * x d) (i j : ℕ) (v : X) :
    (rootOp ρ x i * rootOp ρ x j) v =
      (if i + j ≤ Nat.card Kˣ then (((i + j).choose i : ℕ) : K) else 0) •
        rootOp ρ x (i + j) v := by
  rw [rootOp_mul_expand ρ x hadd i j v, rootOp_mul_expand' ρ x i j v]
  have h3 : (∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
          rootOp ρ x k v) =
      ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        (if k = i + j then (((k.choose i : ℕ) : K)) else 0) • rootOp ρ x k v := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [rootCoeff_mul_binomial (by
      have := Finset.mem_range.mp hk
      omega)]
  rw [h3]
  by_cases hij : i + j ≤ Nat.card Kˣ
  · rw [if_pos hij]
    rw [Finset.sum_eq_single (i + j)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk, zero_smul]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · rw [if_neg hij, zero_smul]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k ≤ Nat.card Kˣ := by
      have := Finset.mem_range.mp hk
      omega
    rw [if_neg (fun h => absurd h (by omega)), zero_smul]

theorem rootOp_mul (hadd : ∀ c d, x (c + d) = x c * x d) (i j : ℕ) :
    rootOp ρ x i * rootOp ρ x j =
      (if i + j ≤ Nat.card Kˣ then (((i + j).choose i : ℕ) : K) else 0) •
        rootOp ρ x (i + j) := by
  ext v
  exact rootOp_mul_apply ρ x hadd i j v

theorem bilin_rootOp_left {B : LinearMap.BilinForm K X}
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadd : ∀ c d, x (c + d) = x c * x d) (u v : X) (k : ℕ) :
    B (rootOp ρ x k u) v = B u (rootOp ρ x k v) := by
  have hx0 : x 0 = 1 := by
    have h : x 0 = x 0 * x 0 := by rw [← hadd 0 0, add_zero]
    exact (mul_left_cancel (a := x 0) (by rw [mul_one]; exact h)).symm
  have hsq : ∀ c : K, x c * x c = 1 := by
    intro c
    rw [← hadd c c, show c + c = 0 from CharTwo.add_self_eq_zero c, hx0]
  have hsym : ∀ c : K, B (ρ (x c) u) v = B u (ρ (x c) v) := by
    intro c
    have hcancel : ρ (x c) (ρ (x c) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, hsq c, map_one, Module.End.one_apply]
    calc B (ρ (x c) u) v
        = B (ρ (x c) u) (ρ (x c) (ρ (x c) v)) := by rw [hcancel]
      _ = B u (ρ (x c) v) := hB (x c) u (ρ (x c) v)
  calc B (rootOp ρ x k u) v
      = B (∑ c : K, rootCoeff k c • ρ (x c) u) v := by rw [rootOp_apply]
    _ = ∑ c : K, rootCoeff k c * B (ρ (x c) u) v := by
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [LinearMap.BilinForm.smul_left]
    _ = ∑ c : K, rootCoeff k c * B u (ρ (x c) v) := by
      exact Finset.sum_congr rfl fun c _ => by rw [hsym c]
    _ = B u (∑ c : K, rootCoeff k c • ρ (x c) v) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun c _ =>
        (LinearMap.BilinForm.smul_right (B := B) (rootCoeff k c) u (ρ (x c) v)).symm
    _ = B u (rootOp ρ x k v) := by rw [rootOp_apply]

theorem forall_rho_eq_iff (hx0 : x 0 = 1) {v : X} :
    (∀ c, ρ (x c) v = v) ↔ ∀ k, 1 ≤ k → rootOp ρ x k v = 0 := by
  constructor
  · intro hfix k hk
    by_cases hkN : k ≤ Nat.card Kˣ
    · rw [rootOp_apply]
      have hsum : (∑ d : K, rootCoeff k d) = 0 := by
        have h := rootCoeff_sum_mul (K := K) hkN (Nat.zero_le _)
        have hk0 : k ≠ 0 := by omega
        simpa [hk0] using h
      calc (∑ d : K, rootCoeff k d • ρ (x d) v)
          = (∑ d : K, rootCoeff k d) • v := by
            rw [Finset.sum_smul]
            exact Finset.sum_congr rfl fun d _ => by rw [hfix d]
        _ = 0 := by rw [hsum, zero_smul]
    · rw [rootOp_of_lt (ρ := ρ) (x := x) (by omega)]
      exact LinearMap.zero_apply v
  · intro hroot c
    rw [rho_eq_sum ρ x c]
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [Finset.sum_eq_single 0]
    · rw [pow_zero, one_smul, rootOp_zero ρ x hx0, Module.End.one_apply]
    · intro k _ hk0
      rw [hroot k (by omega), smul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) hnot

private theorem odd_choose_two_pow_sub_one (f i : ℕ) (hi : i ≤ 2 ^ f - 1) :
    Odd ((2 ^ f - 1).choose i) := by
  have hN : 2 ^ f - 1 < 2 ^ f := by
    have := Nat.two_pow_pos f
    omega
  have hi' : i < 2 ^ f := by omega
  have h := Choose.choose_modEq_prod_range_choose_nat (p := 2) (a := f)
    (n := 2 ^ f - 1) (k := i) hN hi'
  have hprod : (∏ j ∈ Finset.range f,
      ((2 ^ f - 1) / 2 ^ j % 2).choose (i / 2 ^ j % 2)) = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    have hbit : Nat.testBit (2 ^ f - 1) j = true := by
      rw [Nat.testBit_two_pow_sub_one]
      simp [Finset.mem_range.mp hj]
    have hNj : (2 ^ f - 1) / 2 ^ j % 2 = 1 := by
      have hbit' : decide ((2 ^ f - 1) / 2 ^ j % 2 = 1) = true := by
        rwa [Nat.testBit_eq_decide_div_mod_eq] at hbit
      simpa using hbit'
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ j) with h0 | h1
    · rw [hNj, h0]
      norm_num
    · rw [hNj, h1]
      norm_num
  rw [hprod] at h
  exact Nat.odd_iff.mpr (by simpa [Nat.ModEq] using h)

theorem odd_choose_card_units {i : ℕ} (hi : i ≤ Nat.card Kˣ) :
    Odd ((Nat.card Kˣ).choose i) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hq⟩ := FiniteField.card K 2
  have hN : Nat.card Kˣ = 2 ^ (f : ℕ) - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hq]
  rw [hN] at hi ⊢
  exact odd_choose_two_pow_sub_one (f : ℕ) i hi

private theorem exists_odd_choose_decomp {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ l : ℕ, k ≠ 2 ^ l) :
    ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ i ≠ j ∧ i + j = k ∧ Odd (k.choose i) := by
  let l := padicValNat 2 k
  let i := 2 ^ l
  let m := divMaxPow k 2
  have hk0 : k ≠ 0 := by omega
  have hmul : m * i = k := by
    dsimp [m, i, l]
    exact divMaxPow_mul_pow_padicValNat 2 k
  have hi0 : 0 < i := by dsimp [i]; exact Nat.pow_pos (by norm_num)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm, zero_mul] at hmul
      omega
    · exact hm
  have hik : i ≤ k := by
    rw [← hmul]
    exact Nat.le_mul_of_pos_left i hm0
  let j := k - i
  have hsum : i + j = k := by
    dsimp [j]
    exact Nat.add_sub_of_le hik
  have hi_lt_k : i < k := by
    rcases lt_or_eq_of_le hik with hlt | heq
    · exact hlt
    · exfalso
      exact hk l (by simpa [i] using heq.symm)
  have hj0 : 0 < j := by dsimp [j]; exact Nat.sub_pos_of_lt hi_lt_k
  have hij_ne : i ≠ j := by
    intro h
    have hkpow : k = 2 ^ (l + 1) := by
      calc k = i + j := hsum.symm
        _ = i + i := by rw [← h]
        _ = 2 ^ l + 2 ^ l := by rw [show i = 2 ^ l from rfl]
        _ = 2 ^ (l + 1) := by rw [pow_succ]; ring
    exact hk (l + 1) hkpow
  have hm_odd : Odd m := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    simpa [m] using not_dvd_divMaxPow (p := 2) (n := k) (by norm_num) hk0
  obtain ⟨t, ht⟩ := hm_odd
  have hm1 : m - 1 = 2 * t := by omega
  have hj_form : j = (m - 1) * i := by
    dsimp [j]
    calc k - i = m * i - i := by rw [hmul]
      _ = m * i - 1 * i := by rw [one_mul]
      _ = (m - 1) * i := (Nat.mul_sub_right_distrib m 1 i).symm
  have hj_pow : j = 2 ^ (l + 1) * t := by
    rw [hj_form, hm1]
    calc (2 * t) * i = 2 * (t * i) := by ring
      _ = 2 * (i * t) := by rw [mul_comm t i]
      _ = (2 * i) * t := by ring
      _ = 2 ^ (l + 1) * t := by
        congr 1
        dsimp [i]
        rw [pow_succ]
        ring
  have htest : j.testBit l = false := by
    rw [hj_pow, Nat.testBit_two_pow_mul]
    simp
  have hand : i &&& j = 0 := by
    dsimp [i]
    rw [Nat.land_comm, Nat.and_two_pow, htest]
    simp
  have hchoose : Odd (k.choose i) := by
    rw [← hsum]
    exact (CFSG.RepresentationTheory.SL2NatSum.odd_choose_add_iff i j).mpr hand
  exact ⟨i, j, hi0, hj0, hij_ne, hsum, hchoose⟩

theorem rootOp_mul_card_sub (hadd : ∀ c d, x (c + d) = x c * x d) {i : ℕ}
    (hi : i ≤ Nat.card Kˣ) :
    rootOp ρ x i * rootOp ρ x (Nat.card Kˣ - i) = rootOp ρ x (Nat.card Kˣ) := by
  have hcoef : (((Nat.card Kˣ).choose i : ℕ) : K) = 1 := by
    rw [CharTwo.natCast_eq_ite,
      if_neg (Nat.not_even_iff_odd.mpr (odd_choose_card_units (K := K) hi))]
  rw [rootOp_mul ρ x hadd i (Nat.card Kˣ - i), Nat.add_sub_of_le hi, if_pos le_rfl,
    hcoef, one_smul]

theorem exists_rootOp_eq_mul (hadd : ∀ c d, x (c + d) = x c * x d) {k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k ≤ Nat.card Kˣ) (hk : ∀ l : ℕ, k ≠ 2 ^ l) :
    ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ i ≠ j ∧ i + j = k ∧
      rootOp ρ x k = rootOp ρ x i * rootOp ρ x j := by
  obtain ⟨i, j, hi0, hj0, hij, hsum, hodd⟩ := exists_odd_choose_decomp hk1 hk
  refine ⟨i, j, hi0, hj0, hij, hsum, ?_⟩
  have hcoef : ((k.choose i : ℕ) : K) = 1 := by
    rw [CharTwo.natCast_eq_ite, if_neg (Nat.not_even_iff_odd.mpr hodd)]
  rw [rootOp_mul ρ x hadd i j, hsum, if_pos hkN, hcoef, one_smul]

end CFSG.LieType.TorusWeights
