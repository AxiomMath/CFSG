module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.QAut

open QuaternionGroup

section Parity

variable (m : ℕ)

def par : ZMod (2 * 2 ^ m) →+* ZMod 2 := ZMod.castHom (dvd_mul_right 2 _) (ZMod 2)

variable {m}

theorem par_natCast (k : ℕ) : par m (k : ZMod (2 * 2 ^ m)) = (k : ZMod 2) :=
  map_natCast (par m) k

theorem par_val (x : ZMod (2 * 2 ^ m)) : par m x = ((x.val : ℕ) : ZMod 2) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact par_natCast _

theorem par_two : par m 2 = 0 := by
  rw [show (2 : ZMod (2 * 2 ^ m)) = ((2 : ℕ) : ZMod (2 * 2 ^ m)) by norm_cast, par_natCast]
  decide

theorem par_eq_zero_iff {x : ZMod (2 * 2 ^ m)} : par m x = 0 ↔ ∃ l, x = 2 * l := by
  constructor
  · intro h
    rw [par_val, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨(c : ZMod (2 * 2 ^ m)), ?_⟩
    rw [← ZMod.natCast_zmod_val x, hc]
    push_cast
    ring
  · rintro ⟨l, rfl⟩
    rw [map_mul, par_two, zero_mul]

theorem par_eq_one_iff {x : ZMod (2 * 2 ^ m)} : par m x = 1 ↔ ∃ l, x = 2 * l + 1 := by
  constructor
  · intro h
    have h0 : par m (x - 1) = 0 := by rw [map_sub, h, map_one, sub_self]
    obtain ⟨l, hl⟩ := par_eq_zero_iff.mp h0
    exact ⟨l, by rw [← hl]; ring⟩
  · rintro ⟨l, rfl⟩
    have : par m (2 * l) = 0 := par_eq_zero_iff.mpr ⟨l, rfl⟩
    rw [map_add, this, map_one, zero_add]

theorem isUnit_of_par_eq_one {x : ZMod (2 * 2 ^ m)} (h : par m x = 1) : IsUnit x := by
  rw [par_val] at h
  have hodd : Odd x.val := ZMod.natCast_eq_one_iff_odd.mp h
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  have h2 : Nat.Coprime x.val 2 := Nat.coprime_two_right.mpr hodd
  exact Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right _ h2)

theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem par_pow_two (hm : 1 ≤ m) : par m ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) = 0 := by
  rw [par_natCast, Nat.cast_pow, show ((2 : ℕ) : ZMod 2) = 0 by decide,
    zero_pow (by omega)]

end Parity

section Aut

theorem a_pow_nat {n : ℕ} (i : ZMod (2 * n)) (k : ℕ) :
    (a i : QuaternionGroup n) ^ k = a ((k : ZMod (2 * n)) * i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, a_mul_a]
    congr 1
    push_cast
    ring

theorem aut_data {m : ℕ} (hm : 2 ≤ m) (φ : QuaternionGroup (2 ^ m) →* QuaternionGroup (2 ^ m))
    (hφ : Function.Injective φ) :
    ∃ α β : ZMod (2 * 2 ^ m), par m α = 1 ∧ (∀ i, φ (a i) = a (α * i)) ∧
      ∀ i, φ (xa i) = xa (β + α * i) := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have hn4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hord : orderOf (φ (a 1)) = 2 * 2 ^ m := by
    rw [orderOf_injective φ hφ, orderOf_a_one]
  obtain ⟨α, hα⟩ : ∃ α, φ (a 1) = a α := by
    rcases h : φ (a 1) with α | j
    · exact ⟨α, rfl⟩
    · exfalso
      rw [h, orderOf_xa] at hord
      omega
  have hpar : par m α = 1 := by
    rw [hα, orderOf_a] at hord
    have hg : Nat.gcd (2 * 2 ^ m) α.val = 1 := by
      have hpos : 0 < 2 * 2 ^ m := by positivity
      rcases Nat.div_eq_self.mp hord with h0 | h1
      · omega
      · exact h1
    rw [par_val]
    refine ZMod.natCast_eq_one_iff_odd.mpr ?_
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.gcd (2 * 2 ^ m) α.val :=
      Nat.dvd_gcd (dvd_mul_right 2 _) (even_iff_two_dvd.mp hev)
    rw [hg] at h2
    omega
  have hai : ∀ i : ZMod (2 * 2 ^ m), φ (a i) = a (α * i) := by
    intro i
    rw [← ZMod.natCast_zmod_val i, ← a_one_pow, map_pow, hα, a_pow_nat, mul_comm]
  obtain ⟨β, hβ⟩ : ∃ β, φ (xa 0) = xa β := by
    rcases h : φ (xa 0) with k | β
    · exfalso
      have hrel : (xa 0 : QuaternionGroup (2 ^ m)) * a 1 = a (-1) * xa 0 := by
        rw [xa_mul_a, a_mul_xa]
        congr 1
        ring
      have h1 := congrArg φ hrel
      rw [map_mul, map_mul, h, hα, hai (-1), a_mul_a, a_mul_a] at h1
      have h2 := a.inj h1
      have h3 : (2 : ZMod (2 * 2 ^ m)) * α = 0 := by linear_combination h2
      have h4 : (a α : QuaternionGroup (2 ^ m)) ^ 2 = 1 := by
        rw [a_pow_nat, Nat.cast_ofNat, h3, a_zero]
      have h5 := orderOf_dvd_of_pow_eq_one h4
      rw [← hα, hord] at h5
      have h6 := Nat.le_of_dvd (by norm_num) h5
      omega
    · exact ⟨β, rfl⟩
  refine ⟨α, β, hpar, hai, fun i => ?_⟩
  have hxi : (xa i : QuaternionGroup (2 ^ m)) = xa 0 * a i := by
    rw [xa_mul_a, zero_add]
  rw [hxi, map_mul, hβ, hai, xa_mul_a]

end Aut

section Iterate

variable {m : ℕ}

theorem par_pow {α : ZMod (2 * 2 ^ m)} (h : par m α = 1) (k : ℕ) : par m (α ^ k) = 1 := by
  rw [map_pow, h, one_pow]

theorem two_pow_dvd_geom {α : ZMod (2 * 2 ^ m)} (h : par m α = 1) (j : ℕ) :
    ∃ y : ZMod (2 * 2 ^ m), ∑ i ∈ Finset.range (2 ^ j), α ^ i = 2 ^ j * y := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨y, hy⟩ := ih
    have h0 : par m (1 + α ^ (2 ^ j)) = 0 := by
      rw [map_add, map_one, par_pow h]
      decide
    obtain ⟨l, hl⟩ := par_eq_zero_iff.mp h0
    refine ⟨l * y, ?_⟩
    have hsplit : ∑ x ∈ Finset.range (2 ^ j), α ^ (2 ^ j + x) =
        α ^ (2 ^ j) * ∑ i ∈ Finset.range (2 ^ j), α ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => pow_add _ _ _
    rw [pow_succ, mul_two, Finset.sum_range_add, hsplit, hy]
    linear_combination (2 ^ j * y) * hl

theorem geom_eq_zero {α : ZMod (2 * 2 ^ m)} (h : par m α = 1) :
    ∑ i ∈ Finset.range (2 * 2 ^ m), α ^ i = 0 := by
  obtain ⟨y, hy⟩ := two_pow_dvd_geom h (m + 1)
  have h0 : (2 : ZMod (2 * 2 ^ m)) ^ (m + 1) = 0 := by
    calc (2 : ZMod (2 * 2 ^ m)) ^ (m + 1) = ((2 * 2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) := by
          push_cast
          ring
      _ = 0 := ZMod.natCast_self _
  have hr : Finset.range (2 * 2 ^ m) = Finset.range (2 ^ (m + 1)) := by
    rw [pow_succ']
  rw [hr, hy, h0, zero_mul]

theorem pow_eq_one_of_par {α : ZMod (2 * 2 ^ m)} (h : par m α = 1) :
    α ^ (2 * 2 ^ m) = 1 := by
  obtain ⟨u, rfl⟩ := isUnit_of_par_eq_one h
  have h1 := ZMod.pow_totient u
  have h2 : Nat.totient (2 * 2 ^ m) = 2 ^ m := by
    rw [← pow_succ', Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  rw [h2] at h1
  have h3 : (u ^ (2 * 2 ^ m) : (ZMod (2 * 2 ^ m))ˣ) = 1 := by
    calc u ^ (2 * 2 ^ m) = (u ^ 2 ^ m) ^ 2 := pow_mul' u 2 (2 ^ m)
      _ = 1 := by rw [h1, one_pow]
  simpa using congrArg Units.val h3

theorem iter_data {φ : QuaternionGroup (2 ^ m) →* QuaternionGroup (2 ^ m)}
    {α β : ZMod (2 * 2 ^ m)} (ha : ∀ i, φ (a i) = a (α * i))
    (hx : ∀ i, φ (xa i) = xa (β + α * i)) (k : ℕ) :
    (∀ i, (⇑φ)^[k] (a i) = a (α ^ k * i)) ∧
      ∀ i, (⇑φ)^[k] (xa i) = xa (β * ∑ j ∈ Finset.range k, α ^ j + α ^ k * i) := by
  induction k with
  | zero => exact ⟨fun i => by simp, fun i => by simp⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [Function.iterate_succ_apply', ih1, ha]
      congr 1
      ring
    · rw [Function.iterate_succ_apply', ih2, hx, geom_sum_succ]
      congr 1
      ring

theorem iter_eq_self {φ : QuaternionGroup (2 ^ m) →* QuaternionGroup (2 ^ m)}
    {α β : ZMod (2 * 2 ^ m)} (hp : par m α = 1) (ha : ∀ i, φ (a i) = a (α * i))
    (hx : ∀ i, φ (xa i) = xa (β + α * i)) (y : QuaternionGroup (2 ^ m)) :
    (⇑φ)^[2 * 2 ^ m] y = y := by
  obtain ⟨h1, h2⟩ := iter_data ha hx (2 * 2 ^ m)
  rcases y with i | i
  · rw [h1, pow_eq_one_of_par hp, one_mul]
  · rw [h2, pow_eq_one_of_par hp, geom_eq_zero hp, mul_zero, zero_add, one_mul]

end Iterate

section Central

variable {m : ℕ}

theorem n_add_n :
    ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) + ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) = 0 := by
  have h := ZMod.natCast_self (2 * 2 ^ m)
  rw [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [← two_mul]
  exact h

theorem n_ne_zero : ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h1 := Nat.le_of_dvd (by positivity) h
  have h2 : 0 < 2 ^ m := by positivity
  omega

theorem mul_n_of_par_zero {x : ZMod (2 * 2 ^ m)} (h : par m x = 0) :
    x * ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) = 0 := by
  obtain ⟨l, rfl⟩ := par_eq_zero_iff.mp h
  calc 2 * l * ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) =
        l * (((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) + ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) := by ring
    _ = 0 := by rw [n_add_n, mul_zero]

theorem mul_n_of_par_one {x : ZMod (2 * 2 ^ m)} (h : par m x = 1) :
    x * ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) = ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) := by
  obtain ⟨l, rfl⟩ := par_eq_one_iff.mp h
  calc (2 * l + 1) * ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) =
        l * (((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) + ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) +
          ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) := by ring
    _ = ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) := by rw [n_add_n, mul_zero, zero_add]

theorem half_add_half (hm : 1 ≤ m) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m)) =
      ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) := by
  have h2 : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  rw [← Nat.cast_add, h2]

theorem orderOf_a_half (hm : 1 ≤ m) :
    orderOf (a ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m)) : QuaternionGroup (2 ^ m)) = 4 := by
  have h2 : (a ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m)) : QuaternionGroup (2 ^ m)) ^ 2 =
      a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) := by
    rw [a_pow_nat, Nat.cast_ofNat, two_mul, half_add_half hm]
  have hnot :
      ¬ (a ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m)) : QuaternionGroup (2 ^ m)) ^ 2 ^ 1 = 1 := by
    rw [pow_one, h2, ← a_zero]
    intro h
    exact n_ne_zero (a.inj h)
  have hfin : (a ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m)) : QuaternionGroup (2 ^ m)) ^
      2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h2, a_pow_nat, Nat.cast_ofNat, two_mul,
      n_add_n, a_zero]
  rw [orderOf_eq_prime_pow hnot hfin]
  norm_num

theorem a_half_fixed_iff (hm : 1 ≤ m) {α l : ZMod (2 * 2 ^ m)} (hα : α = 2 * l + 1) :
    (a (α * ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m))) : QuaternionGroup (2 ^ m)) =
        a ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m)) ↔ par m l = 0 := by
  have hexp : α * ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m)) =
      ((2 ^ (m - 1) : ℕ) : ZMod (2 * 2 ^ m)) + l * ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) := by
    rw [hα, ← half_add_half hm]
    ring
  rw [hexp]
  constructor
  · intro h
    have h1 := a.inj h
    have h2 : l * ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) = 0 := by linear_combination h1
    rcases zmod_two_cases (par m l) with h0 | h0
    · exact h0
    · exfalso
      rw [mul_n_of_par_one h0] at h2
      exact n_ne_zero h2
  · intro h
    rw [mul_n_of_par_zero h, add_zero]

theorem orderOf_a_of_par {k : ZMod (2 * 2 ^ m)} (hk : par m k = 1) :
    orderOf (a k : QuaternionGroup (2 ^ m)) = 2 * 2 ^ m := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  rw [orderOf_a]
  have hcop : Nat.gcd (2 * 2 ^ m) k.val = 1 := by
    rw [par_val] at hk
    have hodd : Odd k.val := ZMod.natCast_eq_one_iff_odd.mp hk
    have h2 : Nat.Coprime 2 k.val := Nat.coprime_two_left.mpr hodd
    exact Nat.coprime_mul_iff_left.mpr ⟨h2, Nat.Coprime.pow_left m h2⟩
  rw [hcop, Nat.div_one]

end Central

section Transport

variable {G : Type*} [Group G] {Q : Subgroup G} {n : ℕ} (e : ↥Q ≃* QuaternionGroup n)

noncomputable def conjHom {g : G} (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) :
    QuaternionGroup n →* QuaternionGroup n where
  toFun x := e ⟨g * ((e.symm x : ↥Q) : G) * g⁻¹, hg _ (e.symm x).2⟩
  map_one' := by
    rw [← map_one e]
    congr 1
    apply Subtype.ext
    simp
  map_mul' x y := by
    rw [← map_mul e]
    congr 1
    apply Subtype.ext
    show g * ((e.symm (x * y) : ↥Q) : G) * g⁻¹ =
      (g * ((e.symm x : ↥Q) : G) * g⁻¹) * (g * ((e.symm y : ↥Q) : G) * g⁻¹)
    rw [map_mul, Subgroup.coe_mul]
    group

theorem conj_eq {g : G} (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (x : QuaternionGroup n) :
    g * ((e.symm x : ↥Q) : G) * g⁻¹ = ((e.symm (conjHom e hg x) : ↥Q) : G) := by
  show _ = ((e.symm (e ⟨g * ((e.symm x : ↥Q) : G) * g⁻¹, hg _ (e.symm x).2⟩) : ↥Q) : G)
  rw [MulEquiv.symm_apply_apply]

theorem conjHom_injective {g : G} (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) :
    Function.Injective (conjHom e hg) := by
  intro x y hxy
  have h := congrArg (fun z => ((e.symm z : ↥Q) : G)) hxy
  rw [← conj_eq e hg, ← conj_eq e hg] at h
  exact e.symm.injective (Subtype.ext (mul_left_cancel (mul_right_cancel h)))

theorem pow_conj_eq {g : G} (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (k : ℕ) (x : QuaternionGroup n) :
    g ^ k * ((e.symm x : ↥Q) : G) * (g ^ k)⁻¹ =
      ((e.symm ((⇑(conjHom e hg))^[k] x) : ↥Q) : G) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← conj_eq e hg, ← ih]
    group

theorem conj_comp {g h : G} (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hh : ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (x : QuaternionGroup n) :
    (g * h) * ((e.symm x : ↥Q) : G) * (g * h)⁻¹ =
      ((e.symm (conjHom e hg (conjHom e hh x)) : ↥Q) : G) := by
  rw [← conj_eq e hg, ← conj_eq e hh]
  group

theorem comm_of_conj_eq {g q : G} (h : g * q * g⁻¹ = q) : q * g = g * q :=
  (mul_inv_eq_iff_eq_mul.mp h).symm

end Transport

end CFSG.CGT.PushingUpLit.SolKNA.R4.QAut

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.QSub

open CFSG.CGT.PushingUpLit.SolKNA.R4.QAut QuaternionGroup

variable {G : Type*} [Group G] {Q : Subgroup G} {r : ℕ}
  (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))

include e

theorem pow_exponent_comm (hr : 4 ≤ r) {g : G} (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) {x : G}
    (hx : x ∈ Q) : g ^ 2 ^ (r - 1) * x = x * g ^ 2 ^ (r - 1) := by
  obtain ⟨α, β, hp, ha, hxa⟩ := aut_data (show 2 ≤ r - 2 by omega) (conjHom e hg)
    (conjHom_injective e hg)
  have hN : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ']
  obtain ⟨y, rfl⟩ : ∃ y : QuaternionGroup (2 ^ (r - 2)), x = ((e.symm y : ↥Q) : G) :=
    ⟨e ⟨x, hx⟩, by rw [MulEquiv.symm_apply_apply]⟩
  have h1 := pow_conj_eq e hg (2 ^ (r - 1)) y
  rw [hN, iter_eq_self hp ha hxa y] at h1
  rw [hN]
  exact (comm_of_conj_eq h1).symm

theorem exists_comm_of_four (hr : 4 ≤ r) {c₁ c₂ : G} (hc₁ : ∀ q ∈ Q, c₁ * q * c₁⁻¹ ∈ Q)
    (hc₂ : ∀ q ∈ Q, c₂ * q * c₂⁻¹ ∈ Q)
    (hna : ¬ ∃ w ∈ Q, orderOf w = 4 ∧ w * c₁ = c₁ * w) :
    (∃ w ∈ Q, orderOf w = 4 ∧ w * c₂ = c₂ * w) ∨
      ∃ w ∈ Q, orderOf w = 4 ∧ w * (c₁ * c₂) = (c₁ * c₂) * w := by
  have hm : 2 ≤ r - 2 := by omega
  obtain ⟨α₁, β₁, hp₁, ha₁, -⟩ := aut_data hm (conjHom e hc₁) (conjHom_injective e hc₁)
  obtain ⟨α₂, β₂, hp₂, ha₂, -⟩ := aut_data hm (conjHom e hc₂) (conjHom_injective e hc₂)
  obtain ⟨l₁, hl₁⟩ := par_eq_one_iff.mp hp₁
  obtain ⟨l₂, hl₂⟩ := par_eq_one_iff.mp hp₂
  have hu4 : orderOf ((e.symm (a ((2 ^ (r - 2 - 1) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) : ↥Q) : G) =
      4 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_a_half (by omega)]
  have hum : ((e.symm (a ((2 ^ (r - 2 - 1) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) : ↥Q) : G) ∈ Q :=
    (e.symm _).2
  rcases zmod_two_cases (par (r - 2) l₁) with h0 | h0
  · exfalso
    refine hna ⟨_, hum, hu4, comm_of_conj_eq ?_⟩
    rw [conj_eq e hc₁, ha₁, (a_half_fixed_iff (by omega) hl₁).mpr h0]
  · rcases zmod_two_cases (par (r - 2) l₂) with h2 | h2
    · left
      refine ⟨_, hum, hu4, comm_of_conj_eq ?_⟩
      rw [conj_eq e hc₂, ha₂, (a_half_fixed_iff (by omega) hl₂).mpr h2]
    · right
      refine ⟨_, hum, hu4, comm_of_conj_eq ?_⟩
      have hl : α₁ * α₂ = 2 * (2 * l₁ * l₂ + l₁ + l₂) + 1 := by
        rw [hl₁, hl₂]
        ring
      have hpl : par (r - 2) (2 * l₁ * l₂ + l₁ + l₂) = 0 := by
        simp only [map_add, map_mul, par_two, h0, h2]
        decide
      rw [conj_comp e hc₁ hc₂, ha₂, ha₁, ← mul_assoc,
        (a_half_fixed_iff (by omega) hl).mpr hpl]

theorem orderOf_swap_mul (hr : 4 ≤ r) {s : G} (hs : ∀ q ∈ Q, s * q * s⁻¹ ∈ Q)
    (hno : ¬ ∃ w ∈ Q, orderOf w = 4 ∧ w * s = s * w) {q : G} (hq : q ∈ Q)
    (hqX : ∀ i : ZMod (2 * 2 ^ (r - 2)), q ≠ ((e.symm (a i) : ↥Q) : G)) :
    orderOf ((s * q * s⁻¹) * q) = 2 ^ (r - 1) := by
  have hm : 2 ≤ r - 2 := by omega
  have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  obtain ⟨α, β, hp, ha, hxa⟩ := aut_data hm (conjHom e hs) (conjHom_injective e hs)
  obtain ⟨l, hl⟩ := par_eq_one_iff.mp hp
  have hpl : par (r - 2) l = 1 := by
    rcases zmod_two_cases (par (r - 2) l) with h0 | h0
    · exfalso
      refine hno ⟨((e.symm (a ((2 ^ (r - 2 - 1) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) : ↥Q) : G),
        (e.symm _).2, ?_, comm_of_conj_eq ?_⟩
      · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_a_half (by omega)]
      · rw [conj_eq e hs, ha, (a_half_fixed_iff (by omega) hl).mpr h0]
    · exact h0
  have hpβ : par (r - 2) β = 1 := by
    rcases zmod_two_cases (par (r - 2) β) with h0 | h0
    · exfalso
      obtain ⟨b, hb⟩ := par_eq_zero_iff.mp h0
      obtain ⟨v, hv⟩ := (isUnit_of_par_eq_one hpl).exists_right_inv
      have hbj : β + α * (-(b * v)) = -(b * v) := by
        rw [hb, hl]
        linear_combination (-2 * b) * hv
      refine hno ⟨((e.symm (xa (-(b * v))) : ↥Q) : G), (e.symm _).2, ?_, comm_of_conj_eq ?_⟩
      · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_xa]
      · rw [conj_eq e hs, hxa, hbj]
    · exact h0
  obtain ⟨y, hy⟩ : ∃ y : QuaternionGroup (2 ^ (r - 2)), q = ((e.symm y : ↥Q) : G) :=
    ⟨e ⟨q, hq⟩, by rw [MulEquiv.symm_apply_apply]⟩
  rcases y with i | j
  · exact absurd hy (hqX i)
  · have hconj := conj_eq e hs (xa j)
    rw [hxa] at hconj
    have hk : par (r - 2)
        (((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) + j - (β + α * j)) = 1 := by
      rw [map_sub, map_add, map_add, map_mul, par_pow_two (by omega), hpβ, hp]
      generalize par (r - 2) j = c
      revert c
      decide
    have hN : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
      rw [show r - 1 = (r - 2) + 1 by omega, pow_succ']
    rw [hy, hconj, ← Subgroup.coe_mul, ← map_mul e.symm, xa_mul_xa, Subgroup.orderOf_coe,
      MulEquiv.orderOf_eq, orderOf_a_of_par hk, hN]

end CFSG.CGT.PushingUpLit.SolKNA.R4.QSub
