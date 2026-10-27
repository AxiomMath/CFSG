module

public import CFSG.GH74.Uniqueness.SU.SU1BgMaxClass
public import CFSG.GH74.Uniqueness.SU.SU1BgTwoMaxClass
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup DihedralGroup

section DihedralAux

theorem two_mul_eq_zero_zmod_pow {k : ℕ} (hk : 1 ≤ k) (j : ZMod (2 ^ k)) (h : 2 * j = 0) :
    j = 0 ∨ j = ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have : NeZero (2 ^ (k' + 1)) := ⟨by positivity⟩
  have hv := j.val_lt
  have hj : j = ((j.val : ℕ) : ZMod (2 ^ (k' + 1))) := (ZMod.natCast_zmod_val j).symm
  have h2 : (((2 * j.val : ℕ)) : ZMod (2 ^ (k' + 1))) = 0 := by
    rw [Nat.cast_mul, ← hj]
    simpa using h
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨c, hc⟩ := h2
  generalize j.val = v at hv hc hj
  have hpos : 0 < 2 ^ k' := by positivity
  have hpow : 2 ^ (k' + 1) = 2 * 2 ^ k' := by ring
  rw [hpow] at hc hv
  have hc' : v = 2 ^ k' * c := by nlinarith
  have hc2 : c < 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ k' * 2 ≤ 2 ^ k' * c := Nat.mul_le_mul_left _ hcon
    omega
  interval_cases c
  · left
    rw [hj, show v = 0 by simpa using hc']
    simp
  · right
    rw [hj, show v = 2 ^ k' by simpa using hc']
    simp

theorem dihedral_centralizer_sr {k : ℕ} (hk : 1 ≤ k) (i : ZMod (2 ^ k))
    (y : DihedralGroup (2 ^ k)) (hy : y * sr i = sr i * y) :
    y = 1 ∨ y = r ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) ∨ y = sr i ∨
      y = sr (i + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k))) := by
  cases y with
  | r j =>
    rw [r_mul_sr, sr_mul_r] at hy
    have hj : i - j = i + j := sr.inj hy
    have h2 : 2 * j = 0 := by linear_combination (-1 : ZMod (2 ^ k)) * hj
    rcases two_mul_eq_zero_zmod_pow hk j h2 with h0 | h1
    · left; rw [h0]; rfl
    · right; left; rw [h1]
  | sr j =>
    rw [sr_mul_sr, sr_mul_sr] at hy
    have hj : i - j = j - i := r.inj hy
    have h2 : 2 * (j - i) = 0 := by linear_combination (-1 : ZMod (2 ^ k)) * hj
    rcases two_mul_eq_zero_zmod_pow hk (j - i) h2 with h0 | h1
    · right; right; left
      have : j = i := by linear_combination h0
      rw [this]
    · right; right; right
      have : j = i + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by linear_combination h1
      rw [this]

end DihedralAux

section TShape

variable {T : Type} [Group T] [Finite T]

omit [Finite T] in
theorem z_central_of_ker {D : Type} [Group D] (π : T →* D) {z : T} (hz1 : z ≠ 1)
    (hker : ∀ t, π t = 1 ↔ t = 1 ∨ t = z) (t : T) : t * z = z * t := by
  have hπz : π z = 1 := (hker z).2 (Or.inr rfl)
  have h1 : π (t * z * t⁻¹) = 1 := by
    rw [map_mul, map_mul, hπz, mul_one, map_inv, mul_inv_cancel]
  rcases (hker _).1 h1 with h | h
  · exfalso
    apply hz1
    have : z = t⁻¹ * (t * z * t⁻¹) * t := by group
    rw [this, h]
    group
  · calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [h]

omit [Finite T] in
theorem card_ker_eq_two {D : Type} [Group D] (π : T →* D) {z : T} (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hker : ∀ t, π t = 1 ↔ t = 1 ∨ t = z) : Nat.card π.ker = 2 := by
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hk : π.ker = Subgroup.zpowers z := by
    ext t
    rw [MonoidHom.mem_ker, hker]
    constructor
    · rintro (h | h)
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z
    · intro ht
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      rw [← zpow_mod_orderOf, hzo]
      rcases Int.emod_two_eq_zero_or_one m with h0 | h1
      · left; rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h0, zpow_zero]
      · right; rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h1, zpow_one]
  rw [hk, Nat.card_zpowers, hzo]

end TShape

section TShape2

variable {T : Type} [Group T] [Finite T]

omit [Finite T] in
theorem card_map_mul_two {D : Type} [Group D] (π : T →* D) {z : T} (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hker : ∀ t, π t = 1 ↔ t = 1 ∨ t = z) (Q : Subgroup T) (hzQ : z ∈ Q) :
    Nat.card (Q.map π) * 2 = Nat.card Q := by
  have hle : π.ker ≤ Q := by
    intro x hx
    rcases (hker x).1 hx with h | h
    · rw [h]; exact Q.one_mem
    · rw [h]; exact hzQ
  have h := Subgroup.card_ker_mul_card_range (π.comp Q.subtype)
  have hr : (π.comp Q.subtype).range = Q.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : (π.comp Q.subtype).ker = π.ker.subgroupOf Q := by
    rw [Subgroup.subgroupOf, MonoidHom.comap_ker]
  rw [hr, hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    card_ker_eq_two π hz1 hzz hker] at h
  omega

end TShape2

section TShape3

variable {T : Type} [Group T] [Finite T]

@[expose] def rotHom (n : ℕ) : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun a := r (Multiplicative.toAdd a)
  map_one' := rfl
  map_mul' a b := by
    show r (Multiplicative.toAdd a + Multiplicative.toAdd b) = r (Multiplicative.toAdd a) * r (Multiplicative.toAdd b)
    rw [r_mul_r]

theorem rotHom_apply (n : ℕ) (a : Multiplicative (ZMod n)) : rotHom n a = r (Multiplicative.toAdd a) := rfl

omit [Finite T] in
theorem exists_q₀_of_rot (n : ℕ) [NeZero n] (π : T →* DihedralGroup n) {z : T}
    (hker : ∀ t, π t = 1 → t ∈ Subgroup.zpowers z) (Q : Subgroup T)
    (hrot : ∀ q ∈ Q, ∃ j : ZMod n, π q = r j) [Finite T] :
    ∃ q₀ : T, Q ≤ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers z := by
  classical
  let Qc : Subgroup (Multiplicative (ZMod n)) := (Q.map π).comap (rotHom n)
  have : IsCyclic (Multiplicative (ZMod n)) := inferInstance
  have : IsCyclic Qc := Subgroup.isCyclic Qc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Qc)
  have hgmem : rotHom n (g : Multiplicative (ZMod n)) ∈ Q.map π := g.2
  obtain ⟨q₀, hq₀Q, hq₀⟩ := hgmem
  refine ⟨q₀, ?_⟩
  intro q hq
  obtain ⟨j, hj⟩ := hrot q hq
  have hjQc : Multiplicative.ofAdd j ∈ Qc := by
    show rotHom n (Multiplicative.ofAdd j) ∈ Q.map π
    exact ⟨q, hq, by rw [hj]; rfl⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨Multiplicative.ofAdd j, hjQc⟩)
  have hm' : (g : Multiplicative (ZMod n)) ^ m = Multiplicative.ofAdd j := congrArg Subtype.val hm
  have hπ : π (q₀ ^ m) = π q := by
    rw [map_zpow, hq₀, ← map_zpow, hm', hj]
    rfl
  have h1 : π ((q₀ ^ m)⁻¹ * q) = 1 := by rw [map_mul, map_inv, hπ, inv_mul_cancel]
  have hq1 : q = q₀ ^ m * ((q₀ ^ m)⁻¹ * q) := by group
  rw [hq1]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers q₀ m) (hker _ h1)

omit [Finite T] in
theorem exists_reflection (n : ℕ) [NeZero n] (π : T →* DihedralGroup n) {z : T}
    (hker : ∀ t, π t = 1 → t ∈ Subgroup.zpowers z) (Q : Subgroup T)
    (hQnc : ∀ q₀ : T, ¬ Q ≤ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers z) [Finite T] :
    ∃ q ∈ Q, ∃ i : ZMod n, π q = sr i := by
  by_contra hcon
  push Not at hcon
  have hrot : ∀ q ∈ Q, ∃ j : ZMod n, π q = r j := by
    intro q hq
    cases hq' : π q with
    | r j => exact ⟨j, rfl⟩
    | sr j => exact absurd hq' (hcon q hq j)
  obtain ⟨q₀, hq₀⟩ := exists_q₀_of_rot n π hker Q hrot
  exact hQnc q₀ hq₀

end TShape3

section DihedralNe

theorem one_ne_sr' (n : ℕ) (i : ZMod n) : (1 : DihedralGroup n) ≠ sr i := by
  intro h
  rw [DihedralGroup.one_def] at h
  cases h

theorem sr_ne_one' (n : ℕ) (i : ZMod n) : sr i ≠ (1 : DihedralGroup n) := fun h => one_ne_sr' n i h.symm

end DihedralNe

section TShape5

variable {T : Type} [Group T] [Finite T]

theorem not_dihedral {j : ℕ} (hj : 3 ≤ j) (e : T ≃* DihedralGroup (2 ^ j)) {z : T}
    (Q : Subgroup T) (hQcard : Nat.card Q * 2 = Nat.card T)
    (hQu : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = z)
    (hQnc : ∀ q₀ : T, ¬ Q ≤ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers z) : False := by
  classical
  have hn0 : 0 < 2 ^ j := by positivity
  have : NeZero (2 ^ j) := ⟨hn0.ne'⟩
  have hker' : ∀ t, e.toMonoidHom t = 1 → t ∈ Subgroup.zpowers z := by
    intro t h
    have : t = 1 := e.injective (by simpa using h)
    rw [this]; exact Subgroup.one_mem _
  obtain ⟨q, hqQ, a, hqa⟩ := exists_reflection (2 ^ j) e.toMonoidHom hker' Q hQnc
  have hTcard : Nat.card T = 2 * 2 ^ j := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  set Q' := Q.map e.toMonoidHom with hQ'
  have hQ'card : Nat.card Q' = Nat.card Q := Subgroup.card_map_of_injective e.injective
  set R' : Subgroup (DihedralGroup (2 ^ j)) := (rotHom (2 ^ j)).range with hR'
  have hrotinj : Function.Injective (rotHom (2 ^ j)) := by
    intro a b hab
    have := r.inj hab
    exact Multiplicative.toAdd.injective this
  have hR'card : Nat.card R' = 2 ^ j := by
    rw [hR', ← Nat.card_congr (MonoidHom.ofInjective hrotinj).toEquiv]
    simp [ZMod.card]
  have hDcard : Nat.card (DihedralGroup (2 ^ j)) = 2 * 2 ^ j := DihedralGroup.nat_card
  have hQ'idx : Q'.index = 2 := by
    have h1 := Subgroup.card_mul_index Q'
    rw [hQ'card, hDcard] at h1
    have h2 : Nat.card Q = 2 ^ j := by omega
    rw [h2] at h1
    have : 2 ^ j * Q'.index = 2 ^ j * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hn0 this
  have hR'idx : R'.index = 2 := by
    have h1 := Subgroup.card_mul_index R'
    rw [hR'card, hDcard] at h1
    have : 2 ^ j * R'.index = 2 ^ j * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hn0 this
  have hinf : (Q' ⊓ R').index ≤ 4 := by
    have := Subgroup.index_inf_le (H := Q') (K := R')
    rw [hQ'idx, hR'idx] at this
    exact this
  have hinfcard : 4 ≤ Nat.card ↥(Q' ⊓ R') := by
    have h1 := Subgroup.card_mul_index (Q' ⊓ R')
    rw [hDcard] at h1
    have h8 : 8 ≤ 2 ^ j := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(Q' ⊓ R') * (Q' ⊓ R').index ≤ 3 * 4 := Nat.mul_le_mul (by omega) hinf
    omega
  have hne : Q' ⊓ R' ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).1 (by omega)
  obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨b, hb⟩ := hc.2
  have hc_eq : c = r (Multiplicative.toAdd b) := hb.symm
  have hsrQ' : sr a ∈ Q' := ⟨q, hqQ, hqa⟩
  have hprod : sr a * c ∈ Q' := Q'.mul_mem hsrQ' hc.1
  obtain ⟨y₂, hy₂Q, hy₂⟩ := hprod
  rw [hc_eq, sr_mul_r] at hy₂
  have hinv : ∀ y ∈ Q, ∀ w : ZMod (2 ^ j), e.toMonoidHom y = sr w → y = z := by
    intro y hy w hyw
    have h1 : y * y = 1 := by
      apply e.injective
      have : e y = sr w := hyw
      rw [map_mul, this, sr_mul_self, map_one]
    rcases hQu y hy h1 with h | h
    · exfalso
      rw [h, map_one] at hyw
      exact one_ne_sr' _ w hyw
    · exact h
  have h1 := hinv q hqQ a hqa
  have h2 := hinv y₂ hy₂Q _ hy₂
  have hsr : sr a = sr (a + Multiplicative.toAdd b) := by rw [← hqa, ← hy₂, h1, h2]
  have hb0 : Multiplicative.toAdd b = 0 := by
    have := sr.inj hsr
    linear_combination -this
  apply hc1
  apply Subtype.ext
  show c = 1
  rw [hc_eq, hb0]
  rfl

end TShape5

section TShape4

variable {T : Type} [Group T] [Finite T]

theorem tshape (hT : IsPGroup 2 T) {k : ℕ} (hk : 2 ≤ k)
    (π : T →* DihedralGroup (2 ^ k)) (hπ : Function.Surjective π) {z : T} (hz1 : z ≠ 1)
    (hzz : z * z = 1) (hker : ∀ t, π t = 1 ↔ t = 1 ∨ t = z) (Q : Subgroup T) (hzQ : z ∈ Q)
    (hQcard : Nat.card Q * 2 = Nat.card T) (hQu : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = z)
    (hQnc : ∀ q₀ : T, ¬ Q ≤ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers z) :
    (∃ n, IsQuaternionTwoGroup T n) ∨ (∃ n, IsSemidihedralTwoGroup T n) := by
  classical
  have hzc := z_central_of_ker π hz1 hker
  have hker2 := card_ker_eq_two π hz1 hzz hker
  have hn0 : 0 < 2 ^ k := by positivity
  have : NeZero (2 ^ k) := ⟨hn0.ne'⟩
  have hDcard : Nat.card (DihedralGroup (2 ^ k)) = 2 * 2 ^ k := DihedralGroup.nat_card
  have hTcard : Nat.card T = 2 * (2 * 2 ^ k) := by
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [hker2, MonoidHom.range_eq_top.2 hπ, Subgroup.card_top, hDcard] at h1
    omega
  have hQb : Nat.card (Q.map π) * 2 = Nat.card Q := card_map_mul_two π hz1 hzz hker Q hzQ
  have hQbcard : Nat.card (Q.map π) = 2 ^ k := by
    have : Nat.card Q * 2 = 2 * (2 * 2 ^ k) := by rw [hQcard, hTcard]
    omega
  have hQbidx : (Q.map π).index = 2 := by
    have h1 := Subgroup.card_mul_index (Q.map π)
    rw [hQbcard, hDcard] at h1
    have : 2 ^ k * (Q.map π).index = 2 ^ k * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hn0 this

  have hker' : ∀ t, π t = 1 → t ∈ Subgroup.zpowers z := by
    intro t h
    rcases (hker t).1 h with h' | h'
    · rw [h']; exact Subgroup.one_mem _
    · rw [h']; exact Subgroup.mem_zpowers z
  obtain ⟨x, hxQ, i, hxi⟩ := exists_reflection (2 ^ k) π hker' Q hQnc
  set hh : ZMod (2 ^ k) := ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) with hhh
  have hhh0 : hh ≠ 0 := by
    intro h0
    rw [hhh, ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by positivity) h0
    have h2 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hhh2 : hh + hh = 0 := by
    rw [hhh, ← Nat.cast_add]
    have : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [pow_succ]; ring
    rw [this]
    exact ZMod.natCast_self _
  obtain ⟨u, huQ, hu⟩ : ∃ u ∈ Q, π u = r hh := by
    have hsq : r (((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k))) * r (((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k))) ∈ Q.map π :=
      Subgroup.mul_self_mem_of_index_two hQbidx _
    rw [r_mul_r] at hsq
    have h2 : ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) + ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) = hh := by
      rw [hhh, ← Nat.cast_add]
      congr 1
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      simp [pow_succ]; ring
    rw [h2] at hsq
    obtain ⟨u, hu1, hu2⟩ := hsq
    exact ⟨u, hu1, hu2⟩
  have hxx : x * x = z := by
    have h1 : π (x * x) = 1 := by rw [map_mul, hxi, sr_mul_self]
    rcases (hker _).1 h1 with h | h
    · exfalso
      rcases hQu x hxQ h with h' | h'
      · rw [h', map_one] at hxi; exact one_ne_sr' _ i hxi
      · rw [h', (hker z).2 (Or.inr rfl)] at hxi; exact one_ne_sr' _ i hxi
    · exact h
  have huu : u * u = z := by
    have h1 : π (u * u) = 1 := by
      rw [map_mul, hu, r_mul_r, hhh2]; rfl
    rcases (hker _).1 h1 with h | h
    · exfalso
      have hu1 : π u = 1 := by
        rcases hQu u huQ h with h' | h'
        · rw [h', map_one]
        · rw [h']; exact (hker z).2 (Or.inr rfl)
      rw [hu] at hu1
      have : (r hh : DihedralGroup (2 ^ k)) = r 0 := hu1
      exact hhh0 (r.inj this)
    · exact h
  have hxu : x * u ≠ u * x := by
    intro hcomm
    have hsq : (x * u) * (x * u) = 1 := by
      calc (x * u) * (x * u) = x * (u * x) * u := by group
        _ = x * (x * u) * u := by rw [← hcomm]
        _ = (x * x) * (u * u) := by group
        _ = 1 := by rw [hxx, huu, hzz]
    rcases hQu _ (Q.mul_mem hxQ huQ) hsq with h | h
    · have : π (x * u) = 1 := by rw [h, map_one]
      rw [map_mul, hxi, hu, sr_mul_r] at this
      exact sr_ne_one' _ _ this
    · have : π (x * u) = 1 := by rw [h]; exact (hker z).2 (Or.inr rfl)
      rw [map_mul, hxi, hu, sr_mul_r] at this
      exact sr_ne_one' _ _ this
  have hxz : x * z = z * x := hzc x
  have hcent : ∀ y : T, y * x = x * y → y = 1 ∨ y = z ∨ y = x ∨ y = x * z := by
    intro y hy
    have hπy : π y * sr i = sr i * π y := by
      rw [← hxi, ← map_mul, ← map_mul, hy]
    rcases dihedral_centralizer_sr (by omega : 1 ≤ k) i (π y) hπy with h | h | h | h
    · rcases (hker y).1 h with h1 | h1
      · left; exact h1
      · right; left; exact h1
    · exfalso
      have h1 : π (u⁻¹ * y) = 1 := by rw [map_mul, map_inv, hu, h, inv_mul_cancel]
      rcases (hker _).1 h1 with h2 | h2
      · have hyu : y = u := by
          calc y = u * (u⁻¹ * y) := by group
            _ = u := by rw [h2, mul_one]
        rw [hyu] at hy
        exact hxu hy.symm
      · have hyu : y = u * z := by
          calc y = u * (u⁻¹ * y) := by group
            _ = u * z := by rw [h2]
        rw [hyu] at hy
        apply hxu
        have h3 : u * x * z = x * u * z := by
          calc u * x * z = u * (x * z) := mul_assoc _ _ _
            _ = u * (z * x) := by rw [hxz]
            _ = (u * z) * x := (mul_assoc _ _ _).symm
            _ = x * (u * z) := hy
            _ = x * u * z := (mul_assoc _ _ _).symm
        exact (mul_right_cancel h3).symm
    · have h1 : π (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxi, h, inv_mul_cancel]
      rcases (hker _).1 h1 with h2 | h2
      · right; right; left
        calc y = x * (x⁻¹ * y) := by group
          _ = x := by rw [h2, mul_one]
      · right; right; right
        calc y = x * (x⁻¹ * y) := by group
          _ = x * z := by rw [h2]
    · exfalso
      have hπxu : π (x * u) = sr (i + hh) := by rw [map_mul, hxi, hu, sr_mul_r]
      have h1 : π ((x * u)⁻¹ * y) = 1 := by rw [map_mul, map_inv, hπxu, h, inv_mul_cancel]
      rcases (hker _).1 h1 with h2 | h2
      · have hyu : y = x * u := by
          calc y = (x * u) * ((x * u)⁻¹ * y) := by group
            _ = x * u := by rw [h2, mul_one]
        rw [hyu] at hy
        apply hxu
        have h3 : x * (u * x) = x * (x * u) := by
          calc x * (u * x) = x * u * x := (mul_assoc _ _ _).symm
            _ = x * (x * u) := hy
        exact (mul_left_cancel h3).symm
      · have hyu : y = x * u * z := by
          calc y = (x * u) * ((x * u)⁻¹ * y) := by group
            _ = x * u * z := by rw [h2]
        rw [hyu] at hy
        apply hxu
        have h3 : x * (u * x) * z = x * (x * u) * z := by
          calc x * (u * x) * z = x * (u * (x * z)) := by group
            _ = x * (u * (z * x)) := by rw [hxz]
            _ = (x * u * z) * x := by group
            _ = x * (x * u * z) := hy
            _ = x * (x * u) * z := by group
        have h4 := mul_right_cancel h3
        exact (mul_left_cancel h4).symm
  have hCcard : Nat.card (Subgroup.centralizer ({x} : Set T)) ≤ 2 ^ 2 := by
    have hsub : (Subgroup.centralizer ({x} : Set T) : Set T) ⊆ ({1, z, x, x * z} : Set T) := by
      intro y hy
      have hy' : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
      rcases hcent y hy' with h | h | h | h <;> simp [h]
    calc Nat.card (Subgroup.centralizer ({x} : Set T))
        = Set.ncard (Subgroup.centralizer ({x} : Set T) : Set T) := Nat.card_coe_set_eq _
      _ ≤ Set.ncard ({1, z, x, x * z} : Set T) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 ^ 2 := by
        calc Set.ncard ({1, z, x, x * z} : Set T) ≤ Set.ncard ({z, x, x * z} : Set T) + 1 :=
              Set.ncard_insert_le _ _
          _ ≤ (Set.ncard ({x, x * z} : Set T) + 1) + 1 := by
              have := Set.ncard_insert_le z ({x, x * z} : Set T)
              omega
          _ ≤ ((Set.ncard ({x * z} : Set T) + 1) + 1) + 1 := by
              have := Set.ncard_insert_le x ({x * z} : Set T)
              omega
          _ = 4 := by rw [Set.ncard_singleton]
  have h8 : 2 ^ 3 ≤ Nat.card T := by
    rw [hTcard]
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  obtain ⟨m, hm, hγ⟩ := CFSG.GH74.Uniqueness.SU.SU1.b_maximalClass_of_small_centralizer 2
    Nat.prime_two T hT h8 x hCcard
  have h8' : 8 < Nat.card T := by
    rw [hTcard]
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  rcases CFSG.GH74.Uniqueness.SU.SU1.b_two_maximalClass_shape T hT h8' m hm hγ with
    ⟨j, hj, ⟨e⟩⟩ | ⟨j, hj, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exfalso
    have hcard : Nat.card T = 2 * 2 ^ j := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hj3 : 3 ≤ j := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      rw [hTcard] at hcard
      omega
    exact not_dihedral hj3 e Q hQcard hQu hQnc
  · left
    refine ⟨j + 2, ⟨by omega, ?_⟩⟩
    simpa using ⟨e⟩
  · right
    exact ⟨n, hn, ⟨e⟩⟩

end TShape4


end CFSG.GH74.GLS.IVK
