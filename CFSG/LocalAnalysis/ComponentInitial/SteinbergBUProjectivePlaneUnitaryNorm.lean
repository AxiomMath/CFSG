module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem fix_root_of_pow_eq_one {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) {σ : K ≃+* K}
    (hσ : σ ^ p = 1) {μ : K} (hμ : IsPrimitiveRoot μ p) {ξ : K} (hξ : ξ ^ p = 1) : σ ξ = ξ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, -, hk⟩ := hμ.eq_pow_of_pow_eq_one (ξ := σ μ)
    (by rw [← map_pow, hμ.pow_eq_one, map_one])
  have hj : ∀ j : ℕ, (σ ^ j) μ = μ ^ (k ^ j) := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, pow_one]; rfl
    | succ j ih =>
      rw [pow_succ', show (σ * σ ^ j) μ = σ ((σ ^ j) μ) from rfl, ih, map_pow, ← hk, ← pow_mul,
        pow_succ']
  have hmod : k ^ p ≡ k [MOD orderOf μ] := by
    rw [← hμ.eq_orderOf]
    have h1 := ZMod.pow_card (k : ZMod p)
    rw [← Nat.cast_pow] at h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  have hσμ : σ μ = μ := by
    have h1 := hj p
    rw [hσ] at h1
    rw [← hk, ← pow_mod_orderOf, show k % orderOf μ = k ^ p % orderOf μ from hmod.symm,
      pow_mod_orderOf]
    exact h1.symm
  obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hξ
  rw [map_pow, hσμ]

theorem prod_range_two_mul {M : Type*} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∏ j ∈ Finset.range (2 * n), g j = ∏ i ∈ Finset.range n, (g (2 * i) * g (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ,
      ih, Finset.prod_range_succ, mul_assoc]

theorem pow_apply_eq_of_apply_eq {K : Type*} [Field K] {φ : K ≃+* K} {x : K} (hx : φ x = x)
    (n : ℕ) : (φ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, show (φ ^ n * φ) x = (φ ^ n) (φ x) from rfl, hx, ih]

theorem apply_prod_pow_eq {K : Type*} [Field K] {σ : K ≃+* K} {p : ℕ} (hσ : σ ^ p = 1) (z : K) :
    σ (∏ i ∈ Finset.range p, (σ ^ i) z) = ∏ i ∈ Finset.range p, (σ ^ i) z := by
  rw [map_prod]
  have h1 := Finset.prod_range_succ' (fun i => (σ ^ i) z) p
  rw [Finset.prod_range_succ, hσ, pow_zero] at h1
  have h2 : ∀ i ∈ Finset.range p, σ ((σ ^ i) z) = (σ ^ (i + 1)) z := fun i _ => by
    rw [pow_succ']
    rfl
  rw [Finset.prod_congr rfl h2]
  by_cases hz : z = 0
  · subst hz
    simp
  · exact (mul_right_cancel₀ hz h1).symm

theorem exists_fixed_mul_eq {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ τ : K ≃+* K} (hστ : Commute σ τ) (hσ : orderOf σ = p) (hτ : orderOf τ = 2) {m : K}
    (hm : m ≠ 0) (hσm : σ m = m) (hτm : τ m = m) :
    ∃ y : K, y ≠ 0 ∧ σ y = y ∧ y * τ y = m := by
  classical
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  set k := (p + 1) / 2 with hkdef
  have hk : 2 * k = p + 1 := by omega
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hτ2 : τ ^ 2 = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hcop : Nat.Coprime p k := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    have := hp.two_le
    omega
  have hok : orderOf (σ ^ k) = p := by
    rw [orderOf_pow' σ (by omega), hσ, Nat.Coprime.gcd_eq_one hcop, Nat.div_one]
  have hcomm : Commute (σ ^ k) τ := hστ.pow_left k
  set ρ := σ ^ k * τ with hρdef
  have hρ : orderOf ρ = 2 * p := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by
      rw [hok, hτ]
      exact (Nat.coprime_primes hp Nat.prime_two).2 hp2), hok, hτ, mul_comm]
  have hρsq : ρ ^ 2 = σ := by
    rw [hρdef, hcomm.mul_pow, hτ2, mul_one, ← pow_mul, mul_comm k 2, hk, pow_succ, hσp, one_mul]
  set F₀ := FixedPoints.subfield (Subgroup.zpowers ρ) K
  have hρm : ρ ∈ MulAction.stabilizer (K ≃+* K) m := by
    rw [MulAction.mem_stabilizer_iff]
    change (σ ^ k) (τ m) = m
    rw [hτm, pow_apply_eq_of_apply_eq hσm]
  have hmF : m ∈ F₀ := fun g => Subgroup.zpowers_le.2 hρm g.2
  have : Finite F₀ := Subtype.finite
  have hm' : (⟨m, hmF⟩ : F₀) ≠ 0 := fun h0 => hm (congrArg Subtype.val h0)
  obtain ⟨z, hz⟩ := FiniteField.unitsMap_norm_surjective F₀ K (Units.mk0 ⟨m, hmF⟩ hm')
  have hzn : ∏ j ∈ Finset.range (2 * p), (ρ ^ j) (z : K) = m := by
    rw [← hρ, ← algebraMap_norm_fixed]
    have h1 := congrArg Units.val hz
    rw [Units.coe_map, Units.val_mk0] at h1
    change algebraMap F₀ K (Algebra.norm F₀ (z : K)) = m
    rw [show Algebra.norm F₀ (z : K) = ⟨m, hmF⟩ from h1]
    rfl
  set y := ∏ i ∈ Finset.range p, (σ ^ i) (z : K) with hy
  have hy0 : y ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero _).2 z.ne_zero
  have hσy : σ y = y := apply_prod_pow_eq hσp _
  refine ⟨y, hy0, hσy, ?_⟩
  rw [← hzn, prod_range_two_mul, Finset.prod_mul_distrib]
  have heven : ∀ i, (ρ ^ (2 * i)) (z : K) = (σ ^ i) (z : K) := fun i => by
    rw [pow_mul, hρsq]
  have hodd' : ∀ i ∈ Finset.range p, (ρ ^ (2 * i + 1)) (z : K) = (σ ^ k) (τ ((σ ^ i) (z : K))) :=
    fun i _ => by
      have hc : Commute (σ ^ i) (σ ^ k * τ) :=
        (Commute.pow_pow_self σ i k).mul_right (hστ.pow_left i)
      rw [pow_succ, pow_mul, hρsq]
      exact congrArg (fun φ : K ≃+* K => φ (z : K)) hc.eq
  rw [Finset.prod_congr rfl (fun i _ => heven i), Finset.prod_congr rfl hodd', ← map_prod,
    ← map_prod, ← hy, show (σ ^ k) (τ y) = (σ ^ k * τ) y from rfl, hcomm.eq,
    show (τ * σ ^ k) y = τ ((σ ^ k) y) from rfl, pow_apply_eq_of_apply_eq hσy]

variable {r f : ℕ} {K : Type} [Field K]

theorem unitary_norm_mul (h : UnitaryFieldData r f K) (x y : K) :
    h.norm (x * y) = h.norm x * h.norm y := by
  simp only [UnitaryFieldData.norm, map_mul]
  ring

theorem unitary_norm_div (h : UnitaryFieldData r f K) (x y : K) :
    h.norm (x / y) = h.norm x / h.norm y := by
  simp only [UnitaryFieldData.norm, map_div₀]
  ring

theorem unitary_norm_apply (h : UnitaryFieldData r f K) (σ : K ≃+* K) (x : K) :
    h.norm (σ x) = σ (h.norm x) := by
  simp only [UnitaryFieldData.norm, map_mul, map_bar_comm]

theorem bar_norm (h : UnitaryFieldData r f K) (x : K) : h.bar (h.norm x) = h.norm x := by
  simp only [UnitaryFieldData.norm, map_mul, h.bar_bar]
  ring

theorem unitary_norm_ne_zero (h : UnitaryFieldData r f K) {x : K} (hx : x ≠ 0) :
    h.norm x ≠ 0 :=
  mul_ne_zero hx ((map_ne_zero h.bar).2 hx)

theorem exists_bar_ringEquiv (h : UnitaryFieldData r f K) :
    ∃ τ : K ≃+* K, (∀ c, τ c = h.bar c) ∧ orderOf τ = 2 ∧ ∀ σ : K ≃+* K, Commute σ τ := by
  let τ : K ≃+* K :=
    { toFun := h.bar
      invFun := h.bar
      left_inv := h.bar_bar
      right_inv := h.bar_bar
      map_mul' := map_mul h.bar
      map_add' := map_add h.bar }
  refine ⟨τ, fun _ => rfl, ?_, fun σ => ?_⟩
  · refine orderOf_eq_prime (RingEquiv.ext fun c => h.bar_bar c) ?_
    intro h1
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (congrArg (fun φ : K ≃+* K => φ c) h1)
  · exact RingEquiv.ext fun c => map_bar_comm h σ c

theorem exists_unit_norm_ratio (h : UnitaryFieldData r f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = p) {ι : Type*} (t : ι → Kˣ) (ν c₀ : K)
    (hν : ∀ i, h.norm (t i : K) = ν)
    (ht : ∀ i, ∏ j ∈ Finset.range p, (σ ^ j) (t i : K) = c₀) :
    ∃ (b : Kˣ) (u : ι → Kˣ), (∀ i, h.norm (u i : K) = 1) ∧
      ∀ i, (b : K) * t i = u i / σ (u i) := by
  classical
  have := h.finite
  obtain ⟨τ, hτ, hτo, hcomm⟩ := exists_bar_ringEquiv h
  obtain ⟨a, v, hv⟩ := exists_norm_ratio σ t c₀ (fun i => by rw [hσ]; exact ht i)
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨1, fun i => (hι.false i).elim, fun i => (hι.false i).elim,
      fun i => (hι.false i).elim⟩
  set n : ι → K := fun i => h.norm (v i : K) with hn
  have hn0 : ∀ i, n i ≠ 0 := fun i => unitary_norm_ne_zero h (v i).ne_zero
  have hσn0 : ∀ i, σ (n i) ≠ 0 := fun i => (map_ne_zero σ).2 (hn0 i)
  have hratio : ∀ i, h.norm (a : K) * ν = n i / σ (n i) := by
    intro i
    have h1 := congrArg h.norm (hv i)
    rwa [unitary_norm_mul, hν i, unitary_norm_div, unitary_norm_apply] at h1
  have hm : ∀ i, σ (n i₀ / n i) = n i₀ / n i := by
    intro i
    have h1 := (hratio i₀).symm.trans (hratio i)
    rw [div_eq_div_iff (hσn0 i₀) (hσn0 i)] at h1
    rw [map_div₀, div_eq_div_iff (hσn0 i) (hn0 i)]
    linear_combination -h1
  have hτm : ∀ i, τ (n i₀ / n i) = n i₀ / n i := fun i => by
    rw [hτ, map_div₀, hn, bar_norm, bar_norm]
  choose y hy0 hσy hyn using fun i => exists_fixed_mul_eq hp hp2 (hcomm σ) hσ hτo
    (div_ne_zero (hn0 i₀) (hn0 i)) (hm i) (hτm i)
  obtain ⟨w, hw⟩ := h.normHom_surjective
    ⟨(n i₀)⁻¹, h.mem_fixedField.2 (by rw [map_inv₀, hn, bar_norm])⟩
  have hw' : h.norm w = (n i₀)⁻¹ := congrArg Subtype.val hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hw'
    exact inv_ne_zero (hn0 i₀) hw'.symm
  have hσw0 : σ w ≠ 0 := (map_ne_zero σ).2 hw0
  refine ⟨a * Units.mk0 w hw0 / Units.mk0 (σ w) hσw0,
    fun i => v i * Units.mk0 w hw0 * Units.mk0 (y i) (hy0 i), fun i => ?_, fun i => ?_⟩
  · simp only [Units.val_mul, Units.val_mk0]
    have hyN : h.norm (y i) = n i₀ / n i := by rw [UnitaryFieldData.norm, ← hτ]; exact hyn i
    rw [unitary_norm_mul, unitary_norm_mul, hw', hyN]
    change n i * (n i₀)⁻¹ * (n i₀ / n i) = 1
    field_simp [hn0 i, hn0 i₀]
  · have hv' := hv i
    have hσv0 : σ (v i : K) ≠ 0 := (map_ne_zero σ).2 (v i).ne_zero
    rw [eq_div_iff hσv0] at hv'
    simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_mk0, map_mul, hσy i]
    field_simp [hσv0, hσw0, hy0 i]
    linear_combination hv'

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
