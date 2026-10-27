module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.IVK.Lifted.QuatAut

open QuaternionGroup

section Coordinates

variable {N : ℕ}

theorem a_pow (k : ZMod (2 * N)) (m : ℕ) :
    (a k : QuaternionGroup N) ^ m = a ((m : ZMod (2 * N)) * k) := by
  induction m with
  | zero => rw [pow_zero, one_def]; simp
  | succ m ih =>
    rw [pow_succ, ih, a_mul_a]
    congr 1
    push_cast
    ring

theorem a_inj {i j : ZMod (2 * N)} (h : (a i : QuaternionGroup N) = a j) : i = j := by
  injection h

theorem xa_inj {i j : ZMod (2 * N)} (h : (xa i : QuaternionGroup N) = xa j) : i = j := by
  injection h

theorem inv_a' (m : ZMod (2 * N)) : (a m : QuaternionGroup N)⁻¹ = a (-m) :=
  inv_eq_of_mul_eq_one_right (by rw [a_mul_a, add_neg_cancel, a_zero])

theorem two_mul_cast : ((N : ZMod (2 * N)) + N) = 0 := by
  have : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
  push_cast at this
  linear_combination this

theorem inv_xa' (m : ZMod (2 * N)) : (xa m : QuaternionGroup N)⁻¹ = xa ((N : ZMod (2 * N)) + m) := by
  apply inv_eq_of_mul_eq_one_right
  rw [xa_mul_xa, one_def]
  congr 1
  linear_combination two_mul_cast (N := N)

def kOf (α : MulAut (QuaternionGroup N)) : ZMod (2 * N) :=
  match α (a 1) with
  | a k => k
  | xa _ => 0

def jOf (α : MulAut (QuaternionGroup N)) : ZMod (2 * N) :=
  match α (xa 0) with
  | xa j => j
  | a _ => 0

theorem kOf_one : kOf (1 : MulAut (QuaternionGroup N)) = 1 := by
  simp [kOf]

theorem jOf_one : jOf (1 : MulAut (QuaternionGroup N)) = 0 := by
  simp [jOf]

variable [NeZero N]

theorem aut_a_one (hN : 3 ≤ N) (α : MulAut (QuaternionGroup N)) : α (a 1) = a (kOf α) := by
  have h : orderOf (α (a 1)) = 2 * N := by
    rw [MulEquiv.orderOf_eq, orderOf_a_one]
  rcases hα : α (a 1) with k | i
  · simp [kOf, hα]
  · exfalso
    rw [hα, orderOf_xa] at h
    omega

theorem isUnit_kOf (hN : 3 ≤ N) (α : MulAut (QuaternionGroup N)) : IsUnit (kOf α) := by
  have h : orderOf (a (kOf α) : QuaternionGroup N) = 2 * N := by
    rw [← aut_a_one hN α, MulEquiv.orderOf_eq, orderOf_a_one]
  rw [orderOf_a] at h
  have hg : (2 * N).gcd (kOf α).val = 1 := by
    rcases Nat.div_eq_self.1 h with h0 | h1
    · omega
    · exact h1
  have h2 : IsUnit (((kOf α).val : ℕ) : ZMod (2 * N)) :=
    (ZMod.isUnit_iff_coprime _ _).2 (by rwa [Nat.coprime_comm])
  rwa [ZMod.natCast_zmod_val] at h2

theorem aut_a (hN : 3 ≤ N) (α : MulAut (QuaternionGroup N)) (i : ZMod (2 * N)) :
    α (a i) = a (kOf α * i) := by
  have h1 : (a i : QuaternionGroup N) = a 1 ^ i.val := by
    rw [a_one_pow, ZMod.natCast_zmod_val]
  rw [h1, map_pow, aut_a_one hN, a_pow, ZMod.natCast_zmod_val]
  congr 1
  ring

theorem aut_xa_zero (hN : 3 ≤ N) (α : MulAut (QuaternionGroup N)) : α (xa 0) = xa (jOf α) := by
  rcases hα : α (xa 0) with m | j
  · exfalso
    obtain ⟨u, hu⟩ := isUnit_kOf hN α
    have h2 : α (a ((↑u⁻¹ : ZMod (2 * N)) * m)) = α (xa 0) := by
      rw [aut_a hN, ← hu, hα]
      congr 1
      exact Units.mul_inv_cancel_left u m
    have h3 := α.injective h2
    simp at h3
  · simp [jOf, hα]

theorem aut_xa (hN : 3 ≤ N) (α : MulAut (QuaternionGroup N)) (i : ZMod (2 * N)) :
    α (xa i) = xa (jOf α + kOf α * i) := by
  have h1 : (xa i : QuaternionGroup N) = xa 0 * a i := by
    rw [xa_mul_a]
    simp
  rw [h1, map_mul, aut_xa_zero hN, aut_a hN, xa_mul_a]

theorem kOf_mul (hN : 3 ≤ N) (α β : MulAut (QuaternionGroup N)) :
    kOf (α * β) = kOf α * kOf β := by
  have h1 : (α * β) (a 1) = a (kOf α * kOf β) := by
    rw [MulAut.mul_apply, aut_a_one hN β, aut_a hN α]
  have h2 := aut_a_one hN (α * β)
  rw [h1] at h2
  exact (a_inj h2).symm

theorem jOf_mul (hN : 3 ≤ N) (α β : MulAut (QuaternionGroup N)) :
    jOf (α * β) = jOf α + kOf α * jOf β := by
  have h1 : (α * β) (xa 0) = xa (jOf α + kOf α * jOf β) := by
    rw [MulAut.mul_apply, aut_xa_zero hN β, aut_xa hN α]
  have h2 := aut_xa_zero hN (α * β)
  rw [h1] at h2
  exact (xa_inj h2).symm

end Coordinates

section Parity

variable {N : ℕ} [NeZero N]

theorem c2_kOf (hN : 3 ≤ N) (α : MulAut (QuaternionGroup N)) :
    ZMod.castHom (dvd_mul_right 2 N) (ZMod 2) (kOf α) = 1 := by
  have hu := (isUnit_kOf hN α).map (ZMod.castHom (dvd_mul_right 2 N) (ZMod 2))
  generalize ZMod.castHom (dvd_mul_right 2 N) (ZMod 2) (kOf α) = x at hu ⊢
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x with h | h
  · rw [h] at hu
    exact absurd hu not_isUnit_zero
  · exact h

@[expose] def parHom (hN : 3 ≤ N) : MulAut (QuaternionGroup N) →* Multiplicative (ZMod 2) where
  toFun α := Multiplicative.ofAdd (ZMod.castHom (dvd_mul_right 2 N) (ZMod 2) (jOf α))
  map_one' := by simp [jOf_one]
  map_mul' α β := by
    rw [jOf_mul hN, map_add, map_mul, c2_kOf hN, one_mul, ofAdd_add]

theorem parHom_apply (hN : 3 ≤ N) (α : MulAut (QuaternionGroup N)) :
    parHom hN α = Multiplicative.ofAdd (ZMod.castHom (dvd_mul_right 2 N) (ZMod 2) (jOf α)) := rfl

theorem parHom_eq_one_iff (hN : 3 ≤ N) (α : MulAut (QuaternionGroup N)) :
    parHom hN α = 1 ↔ 2 ∣ (jOf α).val := by
  rw [parHom_apply, ofAdd_eq_one]
  have h : ZMod.castHom (dvd_mul_right 2 N) (ZMod 2) (jOf α) = (((jOf α).val : ℕ) : ZMod 2) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (jOf α)]
    exact map_natCast _ _
  rw [h, ZMod.natCast_eq_zero_iff]

omit [NeZero N] in
theorem jOf_eq_of {α : MulAut (QuaternionGroup N)} {J : ZMod (2 * N)} (h : α (xa 0) = xa J) :
    jOf α = J := by
  simp [jOf, h]

theorem parHom_eq_one_of_two_mul (hN : 3 ≤ N) {α : MulAut (QuaternionGroup N)} {i : ZMod (2 * N)}
    (h : jOf α = i + i) : parHom hN α = 1 := by
  rw [parHom_apply, ofAdd_eq_one, h, map_add]
  exact (by decide : ∀ x : ZMod 2, x + x = 0) _

theorem parHom_conj (hN : 3 ≤ N) (q : QuaternionGroup N) : parHom hN (MulAut.conj q) = 1 := by
  rcases q with m | m
  · have h : (MulAut.conj (a m : QuaternionGroup N)) (xa 0) = xa (0 - m + -m) := by
      rw [MulAut.conj_apply, inv_a', a_mul_xa, xa_mul_a]
    apply parHom_eq_one_of_two_mul hN (i := -m)
    rw [jOf_eq_of h]
    ring
  · have h : (MulAut.conj (xa m : QuaternionGroup N)) (xa 0) = xa (m + m) := by
      rw [MulAut.conj_apply, inv_xa', xa_mul_xa, a_mul_xa]
      congr 1
      ring
    exact parHom_eq_one_of_two_mul hN (jOf_eq_of h)

end Parity

section TwoPower

theorem three_le_two_pow (m : ℕ) : 3 ≤ 2 ^ (m + 2) := by
  have : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

theorem isUnit_of_not_dvd {n : ℕ} (x : ZMod (2 * 2 ^ n)) (hx : ¬ 2 ∣ x.val) : IsUnit x := by
  have h2 : (x.val).Coprime (2 ^ (n + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hx).symm
  have h : (x.val).Coprime (2 * 2 ^ n) := by
    have h3 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n
    rwa [h3] at h2
  have := (ZMod.isUnit_iff_coprime x.val (2 * 2 ^ n)).2 h
  rwa [ZMod.natCast_zmod_val] at this

theorem not_dvd_of_isUnit {N : ℕ} [NeZero N] {x : ZMod (2 * N)} (hx : IsUnit x) : ¬ 2 ∣ x.val := by
  intro h2
  have h1 := (ZMod.isUnit_iff_coprime x.val (2 * N)).1 (by rwa [ZMod.natCast_zmod_val])
  have h3 : 2 ∣ Nat.gcd x.val (2 * N) := Nat.dvd_gcd h2 (dvd_mul_right 2 _)
  rw [Nat.Coprime.gcd_eq_one h1] at h3
  omega

end TwoPower

section Criteria

variable {N M : ℕ} [NeZero N]

theorem exists_fixed_of_parHom_eq_one (hNM : N = 4 * M) (hM : 0 < M) (hN : 3 ≤ N)
    (hunit : ∀ x : ZMod (2 * N), ¬ 2 ∣ x.val → IsUnit x)
    (α : MulAut (QuaternionGroup N)) (hp : parHom hN α = 1) :
    ∃ y : QuaternionGroup N, orderOf y = 4 ∧ α y = y := by
  have hkodd : ¬ 2 ∣ (kOf α).val := not_dvd_of_isUnit (isUnit_kOf hN α)
  have hjeven : 2 ∣ (jOf α).val := (parHom_eq_one_iff hN α).1 hp
  have hklt : (kOf α).val < 2 * N := ZMod.val_lt _
  have hkcast : (((kOf α).val : ℕ) : ZMod (2 * N)) = kOf α := ZMod.natCast_zmod_val _
  have hjcast : (((jOf α).val : ℕ) : ZMod (2 * N)) = jOf α := ZMod.natCast_zmod_val _
  have h2N : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
  have hk4 : (kOf α).val % 4 = 1 ∨ (kOf α).val % 4 = 3 := by omega
  rcases hk4 with h1 | h3
  · obtain ⟨q, hq⟩ : ∃ q, (kOf α).val = 4 * q + 1 := ⟨(kOf α).val / 4, by omega⟩
    have hkq : kOf α = 4 * (q : ZMod (2 * N)) + 1 := by
      rw [← hkcast, hq]
      push_cast
      ring
    set Y : ZMod (2 * N) := ((2 * M : ℕ) : ZMod (2 * N)) with hY
    have h4Y : (4 : ZMod (2 * N)) * Y = 0 := by
      have h : (4 : ZMod (2 * N)) * Y = ((4 * (2 * M) : ℕ) : ZMod (2 * N)) := by
        rw [hY]
        push_cast
        ring
      rw [h, show 4 * (2 * M) = 2 * N by omega]
      exact h2N
    refine ⟨a Y, ?_, ?_⟩
    · rw [orderOf_a, hY, ZMod.val_natCast_of_lt (by omega : 2 * M < 2 * N),
        Nat.gcd_eq_right (⟨4, by omega⟩ : 2 * M ∣ 2 * N)]
      exact Nat.div_eq_of_eq_mul_left (by omega : 0 < 2 * M) (by omega)
    · rw [aut_a hN α]
      congr 1
      rw [hkq]
      linear_combination (q : ZMod (2 * N)) * h4Y
  · obtain ⟨q, hq⟩ : ∃ q, (kOf α).val = 4 * q + 3 := ⟨(kOf α).val / 4, by omega⟩
    have hkq : kOf α = 4 * (q : ZMod (2 * N)) + 3 := by
      rw [← hkcast, hq]
      push_cast
      ring
    have hu : ¬ 2 ∣ (((2 * q + 1 : ℕ)) : ZMod (2 * N)).val := by
      rw [ZMod.val_natCast_of_lt (by omega : 2 * q + 1 < 2 * N)]
      omega
    obtain ⟨uu, huu⟩ := hunit _ hu
    obtain ⟨j', hj'⟩ := hjeven
    have hjc : jOf α = 2 * (j' : ZMod (2 * N)) := by
      rw [← hjcast, hj']
      push_cast
      ring
    have huu' : (uu : ZMod (2 * N)) = 2 * (q : ZMod (2 * N)) + 1 := by
      rw [huu]
      push_cast
      ring
    refine ⟨xa (-((j' : ZMod (2 * N)) * (↑uu⁻¹ : ZMod (2 * N)))), orderOf_xa _, ?_⟩
    rw [aut_xa hN α]
    congr 1
    have hmi : (uu : ZMod (2 * N)) * (↑uu⁻¹ : ZMod (2 * N)) = 1 := Units.mul_inv uu
    rw [hjc, hkq]
    linear_combination ((2 * (j' : ZMod (2 * N)) * (↑uu⁻¹ : ZMod (2 * N)))) * huu' +
      (-(2 * (j' : ZMod (2 * N)))) * hmi

theorem no_fixed_of_parHom_ne_one (hN : 3 ≤ N)
    (hunit : ∀ x : ZMod (2 * N), ¬ 2 ∣ x.val → IsUnit x)
    (α : MulAut (QuaternionGroup N)) (hα : α * α = 1) (hp : parHom hN α ≠ 1) :
    ¬ ∃ y : QuaternionGroup N, orderOf y = 4 ∧ α y = y := by
  rintro ⟨y, hy4, hyα⟩
  have hjodd : ¬ 2 ∣ (jOf α).val := fun h => hp ((parHom_eq_one_iff hN α).2 h)
  have hjunit : IsUnit (jOf α) := hunit _ hjodd
  have hjk : jOf α + kOf α * jOf α = 0 := by
    have := jOf_mul hN α α
    rw [hα, jOf_one] at this
    exact this.symm
  have hk : kOf α = -1 := by
    have h1 : jOf α * (1 + kOf α) = 0 := by linear_combination hjk
    have h2 := (hjunit.mul_right_eq_zero).1 h1
    linear_combination h2
  rcases y with i | i
  · rw [aut_a hN α, hk, neg_one_mul] at hyα
    have h2 := a_inj hyα
    have h3 : (a i : QuaternionGroup N) ^ 2 = 1 := by
      rw [pow_two, a_mul_a, ← a_zero]
      congr 1
      linear_combination (-1 : ZMod (2 * N)) * h2
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hy4] at h4
    omega
  · rw [aut_xa hN α, hk] at hyα
    have h2 := xa_inj hyα
    exact hp (parHom_eq_one_of_two_mul hN (i := i) (by linear_combination h2))

end Criteria

section Interface

theorem exists_parity_hom {H : Type*} [Group H] (n : ℕ) (hn : 2 ≤ n)
    (e : QuaternionGroup (2 ^ n) ≃* H) :
    ∃ π : MulAut H →* Multiplicative (ZMod 2), (∀ p : H, π (MulAut.conj p) = 1) ∧
      ∀ α : MulAut H, α * α = 1 → ((∃ y : H, orderOf y = 4 ∧ α y = y) ↔ π α = 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hN : 3 ≤ 2 ^ (m + 2) := three_le_two_pow m
  have hNM : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  have hM : 0 < 2 ^ m := by positivity
  have hunit : ∀ x : ZMod (2 * 2 ^ (m + 2)), ¬ 2 ∣ x.val → IsUnit x :=
    fun x hx => isUnit_of_not_dvd x hx
  refine ⟨(parHom hN).comp (MulAut.congr e.symm).toMonoidHom, ?_, ?_⟩
  · intro p
    have h : MulAut.congr e.symm (MulAut.conj p) = MulAut.conj (e.symm p) := by
      ext x
      simp [MulAut.congr_apply, MulAut.conj_apply]
    show parHom hN (MulAut.congr e.symm (MulAut.conj p)) = 1
    rw [h]
    exact parHom_conj hN _
  · intro α hα
    have hα' : MulAut.congr e.symm α * MulAut.congr e.symm α = 1 := by
      rw [← map_mul, hα, map_one]
    constructor
    · rintro ⟨y, hy4, hyα⟩
      by_contra hne
      refine no_fixed_of_parHom_ne_one hN hunit _ hα' hne ⟨e.symm y, ?_, ?_⟩
      · rw [MulEquiv.orderOf_eq]
        exact hy4
      · simp [MulAut.congr_apply, hyα]
    · intro h
      obtain ⟨y, hy4, hyα⟩ := exists_fixed_of_parHom_eq_one hNM hM hN hunit _ h
      refine ⟨e y, ?_, ?_⟩
      · rw [MulEquiv.orderOf_eq]
        exact hy4
      · have h1 := congrArg e hyα
        simpa [MulAut.congr_apply] using h1

end Interface

end CFSG.GH74.GLS.IVK.Lifted.QuatAut
