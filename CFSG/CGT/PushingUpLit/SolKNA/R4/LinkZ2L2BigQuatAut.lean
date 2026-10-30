module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.QuatAutH

open QuaternionGroup

variable {n : ℕ}

theorem n_add_n : (n : ZMod (2 * n)) + n = 0 := by
  rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]

theorem n_ne_zero [NeZero n] : (n : ZMod (2 * n)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (NeZero.pos n) h
  have := NeZero.pos n
  omega

theorem add_self_eq_zero_iff [NeZero n] (i : ZMod (2 * n)) :
    i + i = 0 ↔ i = 0 ∨ i = n := by
  constructor
  · intro h
    have hv := ZMod.val_lt i
    rw [← ZMod.natCast_zmod_val i, ← Nat.cast_add, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have hk2 : k < 2 := by
      by_contra hk2
      have : 2 * n * 2 ≤ 2 * n * k := Nat.mul_le_mul_left _ (not_lt.mp hk2)
      omega
    interval_cases k
    · left
      rw [← ZMod.natCast_zmod_val i]
      have : i.val = 0 := by omega
      rw [this, Nat.cast_zero]
    · right
      rw [← ZMod.natCast_zmod_val i]
      have : i.val = n := by omega
      rw [this]
  · rintro (rfl | rfl)
    · exact add_zero 0
    · exact n_add_n

theorem mul_self_eq_one_iff [NeZero n] (w : QuaternionGroup n) :
    w * w = 1 ↔ w = a 0 ∨ w = a n := by
  rcases w with i | i
  · rw [a_mul_a, one_def, a.injEq, add_self_eq_zero_iff, a.injEq, a.injEq]
  · rw [xa_mul_xa, one_def, a.injEq, add_sub_cancel_right]
    simp only [reduceCtorEq, or_self, iff_false]
    exact n_ne_zero

theorem a_pow' (κ : ZMod (2 * n)) (m : ℕ) : (a κ : QuaternionGroup n) ^ m = a ((m : ZMod (2 * n)) * κ) := by
  induction m with
  | zero => rw [pow_zero, one_def, Nat.cast_zero, zero_mul]
  | succ m ih =>
    rw [pow_succ, ih, a_mul_a]
    congr 1
    push_cast
    ring

theorem coords (hn : 2 < n) (φ : MulAut (QuaternionGroup n)) :
    ∃ κ γ : ZMod (2 * n), ∀ i, φ (a i) = a (κ * i) ∧ φ (xa i) = xa (γ + κ * i) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, φ (a 1) = a κ := by
    rcases h : φ (a 1) with κ | κ
    · exact ⟨κ, rfl⟩
    · exfalso
      have h1 := MulEquiv.orderOf_eq φ (a 1)
      rw [h, orderOf_xa, orderOf_a_one] at h1
      omega
  have ha : ∀ i, φ (a i) = a (κ * i) := by
    intro i
    rw [← ZMod.natCast_zmod_val i, ← a_one_pow, map_pow, hκ, a_pow', mul_comm]
  obtain ⟨γ, hγ⟩ : ∃ γ, φ (xa 0) = xa γ := by
    rcases h : φ (xa 0) with j | j
    · exfalso
      have hc : φ (xa 0 * a 1) = φ (a 1 * xa 0) := by
        rw [map_mul, map_mul, h, hκ, a_mul_a, a_mul_a, add_comm]
      have h0 := φ.injective hc
      rw [xa_mul_a, a_mul_xa, xa.injEq] at h0
      have h2 : ((2 : ℕ) : ZMod (2 * n)) = 0 := by push_cast; linear_combination h0
      rw [ZMod.natCast_eq_zero_iff] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact ⟨j, rfl⟩
  refine ⟨κ, γ, fun i => ⟨ha i, ?_⟩⟩
  have : (xa i : QuaternionGroup n) = xa 0 * a i := by rw [xa_mul_a, zero_add]
  rw [this, map_mul, hγ, ha, xa_mul_a]

def IsTransl (φ : MulAut (QuaternionGroup n)) (t : ZMod (2 * n)) : Prop :=
  ∀ i, φ (a i) = a i ∧ φ (xa i) = xa (t + i)

theorem IsTransl.mul {φ ψ : MulAut (QuaternionGroup n)} {s t : ZMod (2 * n)}
    (hφ : IsTransl φ s) (hψ : IsTransl ψ t) : IsTransl (φ * ψ) (s + t) := by
  intro i
  rw [MulAut.mul_apply, MulAut.mul_apply, (hψ i).1, (hφ i).1, (hψ i).2, (hφ _).2, add_assoc]
  exact ⟨rfl, rfl⟩

theorem IsTransl.pow {φ : MulAut (QuaternionGroup n)} {s : ZMod (2 * n)} (hφ : IsTransl φ s)
    (m : ℕ) : IsTransl (φ ^ m) (m * s) := by
  induction m with
  | zero =>
    intro i
    rw [pow_zero, Nat.cast_zero, zero_mul, zero_add]
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    have e : ((m + 1 : ℕ) : ZMod (2 * n)) * s = m * s + s := by push_cast; ring
    rw [pow_succ, e]
    exact ih.mul hφ

theorem IsTransl.eq_one {φ : MulAut (QuaternionGroup n)} (hφ : IsTransl φ 0) : φ = 1 := by
  ext x
  rcases x with i | i
  · exact (hφ i).1
  · rw [(hφ i).2, zero_add]
    rfl

theorem two_mul_eq_zero {h j : ℕ} (hn : n = 2 ^ (j + 2)) (hh : h = 2 ^ (j + 1))
    (x d : ZMod (2 * n)) (hd : (h : ZMod (2 * n)) * d ≠ 0) (hx : x * d = 0) : x + x = 0 := by
  haveI : NeZero n := ⟨by rw [hn]; positivity⟩
  have hN : 2 * n = 2 ^ (j + 3) := by rw [hn]; ring
  rw [← ZMod.natCast_zmod_val d] at hd hx
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [Ne, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hd
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
  rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  generalize d.val = D at hd hx
  generalize x.val = X at hx ⊢
  rw [hN] at hd hx ⊢
  rw [hh] at hd
  have hD : D ≠ 0 := by
    rintro rfl
    exact hd (by rw [mul_zero]; exact dvd_zero _)
  obtain ⟨e, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hD
  have he : e < 2 := by
    by_contra he
    apply hd
    obtain ⟨c, rfl⟩ : ∃ c, e = c + 2 := ⟨e - 2, by omega⟩
    exact ⟨2 ^ c * o, by ring⟩
  have hcop : Nat.Coprime (2 ^ (j + 3)) o :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ho)
  have h2 : 2 ^ (j + 3) ∣ X * 2 ^ e :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop (by rwa [← mul_assoc] at hx)
  interval_cases e
  · rw [pow_zero, mul_one] at h2
    exact dvd_add h2 h2
  · rwa [pow_one, mul_two] at h2

theorem arith_false {h j : ℕ} (hn : n = 2 ^ (j + 2)) (hh : h = 2 ^ (j + 1))
    (κ l γ δ : ZMod (2 * n)) (hκ : κ * κ = 1)
    (E1 : γ + κ * (δ + l * γ) = δ) (E2 : δ + l * δ = h * (γ + κ * γ))
    (E3 : (h : ZMod (2 * n)) * (γ + κ * γ) ≠ 0)
    (E4 : γ + κ * γ + (δ + l * (γ + κ * γ)) = δ) : False := by
  haveI : NeZero n := ⟨by rw [hn]; positivity⟩
  have hnh : n = 2 * h := by rw [hn, hh]; ring
  have hNN : (n : ZMod (2 * n)) * n = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact Dvd.intro h (by rw [hnh]; ring)
  have hH2 : (h : ZMod (2 * n)) * 2 = n := by
    have : ((h * 2 : ℕ) : ZMod (2 * n)) = ((n : ℕ) : ZMod (2 * n)) := by
      rw [show h * 2 = n by omega]
    push_cast at this
    exact this
  have Z := two_mul_eq_zero hn hh
  have h1 : (1 + l) + (1 + l) = 0 := Z _ _ E3 (by linear_combination E4)
  have h2 : (κ - 1) + (κ - 1) = 0 := Z _ _ E3 (by linear_combination γ * hκ)
  rcases (add_self_eq_zero_iff _).mp h1 with hl | hl
  · exact E3 (by linear_combination -E2 + δ * hl)
  obtain rfl : l = n - 1 := by linear_combination hl
  rcases (add_self_eq_zero_iff _).mp h2 with hk | hk
  · obtain rfl : κ = 1 := by linear_combination hk
    exact E3 (by linear_combination γ * hH2 + E1)
  · obtain rfl : κ = n + 1 := by linear_combination hk
    exact E3 (by linear_combination -E2 + E1 - γ * hNN)

theorem not_injective {j : ℕ} (hn : n = 2 ^ (j + 2))
    (f : QuaternionGroup n →* MulAut (QuaternionGroup n)) : ¬ Function.Injective f := by
  intro hf
  have h4 : 2 ^ 2 ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn2 : 2 < n := by rw [hn]; norm_num at h4; omega
  haveI : NeZero n := ⟨by omega⟩
  set α := f (a 1) with hαdef
  set β := f (xa 0) with hβdef
  obtain ⟨κ, γ, hα⟩ := coords hn2 α
  obtain ⟨l, δ, hβ⟩ := coords hn2 β
  have hαa : ∀ i, α (a i) = a (κ * i) := fun i => (hα i).1
  have hαx : ∀ i, α (xa i) = xa (γ + κ * i) := fun i => (hα i).2
  have hβa : ∀ i, β (a i) = a (l * i) := fun i => (hβ i).1
  have hβx : ∀ i, β (xa i) = xa (δ + l * i) := fun i => (hβ i).2
  obtain ⟨l', hl'⟩ : ∃ l', l' * l = 1 := by
    obtain ⟨μ, μ', hμ⟩ := coords hn2 β.symm
    have e := MulEquiv.apply_symm_apply β (a 1)
    rw [(hμ 1).1, hβa, a.injEq] at e
    exact ⟨μ, by linear_combination e⟩
  have R1 : α * β * α = β := by
    rw [hαdef, hβdef, ← map_mul, ← map_mul, a_mul_xa, xa_mul_a, sub_add_cancel]
  have e1 := DFunLike.congr_fun R1 (a 1)
  simp only [MulAut.mul_apply, hαa, hβa, a.injEq, mul_one] at e1
  have hκ2 : κ * κ = 1 := by linear_combination l' * e1 - (κ * κ - 1) * hl'
  set d := γ + κ * γ with hd
  have hσ : IsTransl (α * α) d := by
    intro i
    rw [MulAut.mul_apply, MulAut.mul_apply, hαa, hαa, hαx, hαx]
    constructor
    · congr 1; linear_combination i * hκ2
    · congr 1; linear_combination i * hκ2
  obtain ⟨h, hh⟩ : ∃ h, h = 2 ^ (j + 1) := ⟨_, rfl⟩
  have hnh : n = 2 * h := by rw [hn, hh]; ring
  have hfan : f (a n) = α ^ n := by rw [← a_one_pow, map_pow]
  have hpow : IsTransl (α ^ n) (h * d) := by
    have : α ^ n = (α * α) ^ h := by rw [← sq, ← pow_mul, ← hnh]
    rw [this]
    exact hσ.pow h
  have R2 : β * β = α ^ n := by
    rw [hβdef, ← map_mul, xa_mul_xa, add_zero, sub_zero, hfan]
  have e2 := DFunLike.congr_fun R2 (xa 0)
  rw [MulAut.mul_apply, hβx, hβx, (hpow 0).2, xa.injEq] at e2
  have E3 : (h : ZMod (2 * n)) * d ≠ 0 := by
    intro h0
    rw [h0] at hpow
    have h1 : f (a n) = f 1 := by rw [hfan, hpow.eq_one, map_one]
    have := hf h1
    rw [one_def, a.injEq] at this
    exact n_ne_zero this
  have R3 : (α * α) * β * (α * α) = β := by
    calc (α * α) * β * (α * α) = α * (α * β * α) * α := by simp only [mul_assoc]
      _ = β := by rw [R1, R1]
  have e4 := DFunLike.congr_fun R3 (xa 0)
  rw [MulAut.mul_apply, MulAut.mul_apply, (hσ 0).2, hβx, (hσ _).2, hβx, xa.injEq] at e4
  have e1x := DFunLike.congr_fun R1 (xa 0)
  rw [MulAut.mul_apply, MulAut.mul_apply, hαx, hβx, hαx, hβx, xa.injEq] at e1x
  exact arith_false hn hh κ l γ δ hκ2 (by linear_combination e1x) (by linear_combination e2) E3
    (by linear_combination e4)

theorem center_mem_ker {M : Type*} [Group M] {j : ℕ} (hn : n = 2 ^ (j + 2))
    (f : QuaternionGroup n →* M) (hf : ¬ Function.Injective f) : f (a n) = 1 := by
  haveI : NeZero n := ⟨by rw [hn]; positivity⟩
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y, f x = f y ∧ x ≠ y := by
    unfold Function.Injective at hf
    push Not at hf
    exact hf
  have hg : f (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hg1 : x⁻¹ * y ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  have hcard : Nat.card (QuaternionGroup n) = 2 ^ (j + 4) := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card, hn]; ring
  have hdvd : orderOf (x⁻¹ * y) ∣ 2 ^ (j + 4) := hcard ▸ orderOf_dvd_natCard _
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := by
    rcases s with _ | t
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hs, pow_zero])) hg1
    · exact ⟨t, rfl⟩
  have hw1 : (x⁻¹ * y) ^ 2 ^ t * (x⁻¹ * y) ^ 2 ^ t = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hs, pow_orderOf_eq_one]
  have hw2 : (x⁻¹ * y) ^ 2 ^ t ≠ 1 := by
    intro h0
    have := orderOf_dvd_of_pow_eq_one h0
    rw [hs] at this
    have := Nat.le_of_dvd (by positivity) this
    have := Nat.pow_lt_pow_right (a := 2) (by norm_num) (Nat.lt_succ_self t)
    omega
  rcases (mul_self_eq_one_iff _).mp hw1 with h0 | h0
  · exact absurd (h0.trans (one_def).symm) hw2
  · rw [← h0, map_pow, hg, one_pow]

theorem hom_centralizes {Y : Type*} [Group Y] {j : ℕ} (hn : n = 2 ^ (j + 2)) (B : Subgroup Y)
    (eB : ↥B ≃* QuaternionGroup n) (f : QuaternionGroup n →* Y)
    (hf : ∀ x, f x ∈ Subgroup.normalizer (B : Set Y)) :
    ∀ b ∈ B, f (a n) * b = b * f (a n) := by
  let φ : QuaternionGroup n →* MulAut B :=
    (Subgroup.normalizerMonoidHom B).comp (f.codRestrict _ hf)
  let ψ : QuaternionGroup n →* MulAut (QuaternionGroup n) :=
    ((MulAut.congr eB).toMonoidHom).comp φ
  have h1 : ψ (a n) = 1 := center_mem_ker hn ψ (not_injective hn ψ)
  have h2 : φ (a n) = 1 := by
    have : (MulAut.congr eB) (φ (a n)) = 1 := h1
    exact (MulAut.congr eB).injective (this.trans (map_one _).symm)
  intro b hb
  have h3 := congrArg (fun m : MulAut B => ((m ⟨b, hb⟩ : B) : Y)) h2
  have h4 : f (a n) * b * (f (a n))⁻¹ = b := h3
  calc f (a n) * b = (f (a n) * b * (f (a n))⁻¹) * f (a n) := by group
    _ = b * f (a n) := by rw [h4]

theorem hom_centralizes_of_four_le {Y : Type*} [Group Y] {r : ℕ} (hr : 4 ≤ r) (B : Subgroup Y)
    (eB : ↥B ≃* QuaternionGroup (2 ^ (r - 2))) (f : QuaternionGroup (2 ^ (r - 2)) →* Y)
    (hf : ∀ x, f x ∈ Subgroup.normalizer (B : Set Y)) :
    ∀ b ∈ B, f (a (2 ^ (r - 2) : ℕ)) * b = b * f (a (2 ^ (r - 2) : ℕ)) :=
  hom_centralizes (j := r - 4) (by congr 1; omega) B eB f hf

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.QuatAutH
