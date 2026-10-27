module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I2013Aux

open Equiv

variable {α : Type} [DecidableEq α]

private theorem rot3 (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    swap x y * swap y z = swap y z * swap z x := by
  have := hxy.symm; have := hxz.symm; have := hyz.symm
  ext i
  by_cases h1 : i = x
  · rw [h1]; simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  by_cases h2 : i = y
  · rw [h2]; simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  by_cases h3 : i = z
  · rw [h3]; simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]

private theorem three_cube (p q r : α) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (swap p q * swap q r) ^ 3 = 1 := by
  have := hpq.symm; have := hpr.symm; have := hqr.symm
  have hp : (swap p q * swap q r) p = q := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hq : (swap p q * swap q r) q = r := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hr : (swap p q * swap q r) r = p := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  ext i
  by_cases h1 : i = p
  · rw [h1]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hp, hq, hr]
  by_cases h2 : i = q
  · rw [h2]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hp, hq, hr]
  by_cases h3 : i = r
  · rw [h3]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hp, hq, hr]
  simp [pow_succ, Perm.mul_apply, swap_apply_of_ne_of_ne, *]

private theorem four_cube (x y z w : α) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) :
    ((swap w y * swap y z) * (swap x y * swap y z)⁻¹) ^ 3 = 1 ∧
      ((swap w y * swap y z) * (swap x y * swap y z)⁻¹) x = w := by
  have := hxy.symm; have := hxz.symm; have := hxw.symm; have := hyz.symm
  have := hyw.symm; have := hzw.symm
  simp only [mul_inv_rev, swap_inv]
  have hx : (swap w y * swap y z * (swap y z * swap x y)) x = w := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hw : (swap w y * swap y z * (swap y z * swap x y)) w = y := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hy : (swap w y * swap y z * (swap y z * swap x y)) y = x := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hz : (swap w y * swap y z * (swap y z * swap x y)) z = z := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  refine ⟨?_, hx⟩
  ext i
  by_cases h1 : i = x
  · rw [h1]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hx, hw, hy]
  by_cases h2 : i = w
  · rw [h2]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hx, hw, hy]
  by_cases h3 : i = y
  · rw [h3]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hx, hw, hy]
  by_cases h4 : i = z
  · rw [h4]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hz]
  simp [pow_succ, Perm.mul_apply, swap_apply_of_ne_of_ne, *]

private theorem five_pow (s q r u v : α) (hsq : s ≠ q) (hsr : s ≠ r) (hsu : s ≠ u) (hsv : s ≠ v)
    (hqr : q ≠ r) (hqu : q ≠ u) (hqv : q ≠ v) (hru : r ≠ u) (hrv : r ≠ v) (huv : u ≠ v) :
    ((swap u s * swap s v) * (swap s q * swap q r)⁻¹) ^ 5 = 1 ∧
      ((swap u s * swap s v) * (swap s q * swap q r)⁻¹) u = s := by
  have := hsq.symm; have := hsr.symm; have := hsu.symm; have := hsv.symm
  have := hqr.symm; have := hqu.symm; have := hqv.symm; have := hru.symm; have := hrv.symm
  have := huv.symm
  simp only [mul_inv_rev, swap_inv]
  have hs : (swap u s * swap s v * (swap q r * swap s q)) s = r := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hr : (swap u s * swap s v * (swap q r * swap s q)) r = q := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hq : (swap u s * swap s v * (swap q r * swap s q)) q = v := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hv : (swap u s * swap s v * (swap q r * swap s q)) v = u := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hu : (swap u s * swap s v * (swap q r * swap s q)) u = s := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  refine ⟨?_, hu⟩
  ext i
  by_cases h1 : i = s
  · rw [h1]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hs, hr, hq, hv, hu]
  by_cases h2 : i = q
  · rw [h2]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hs, hr, hq, hv, hu]
  by_cases h3 : i = r
  · rw [h3]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hs, hr, hq, hv, hu]
  by_cases h4 : i = u
  · rw [h4]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hs, hr, hq, hv, hu]
  by_cases h5 : i = v
  · rw [h5]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hs, hr, hq, hv, hu]
  have hf : (swap u s * swap s v * (swap q r * swap s q)) i = i := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  simp [pow_succ, Perm.mul_apply, hf]

private theorem disj_cube (x y z u a b : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hua : u ≠ a) (hub : u ≠ b) (hab : a ≠ b)
    (hux : u ≠ x) (huy : u ≠ y) (huz : u ≠ z) (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z)
    (hbx : b ≠ x) (hby : b ≠ y) (hbz : b ≠ z) :
    ((swap u a * swap a b) * (swap x y * swap y z)⁻¹) ^ 3 = 1 ∧
      ((swap u a * swap a b) * (swap x y * swap y z)⁻¹) u = a := by
  have := hxy.symm; have := hxz.symm; have := hyz.symm; have := hua.symm; have := hub.symm
  have := hab.symm; have := hux.symm; have := huy.symm; have := huz.symm; have := hax.symm
  have := hay.symm; have := haz.symm; have := hbx.symm; have := hby.symm; have := hbz.symm
  simp only [mul_inv_rev, swap_inv]
  have hx : (swap u a * swap a b * (swap y z * swap x y)) x = z := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hz : (swap u a * swap a b * (swap y z * swap x y)) z = y := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hy : (swap u a * swap a b * (swap y z * swap x y)) y = x := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hu : (swap u a * swap a b * (swap y z * swap x y)) u = a := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have ha : (swap u a * swap a b * (swap y z * swap x y)) a = b := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hb : (swap u a * swap a b * (swap y z * swap x y)) b = u := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  refine ⟨?_, hu⟩
  ext i
  by_cases h1 : i = x
  · rw [h1]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hx, hz, hy, hu, ha, hb]
  by_cases h2 : i = y
  · rw [h2]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hx, hz, hy, hu, ha, hb]
  by_cases h3 : i = z
  · rw [h3]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hx, hz, hy, hu, ha, hb]
  by_cases h4 : i = u
  · rw [h4]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hx, hz, hy, hu, ha, hb]
  by_cases h5 : i = a
  · rw [h5]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hx, hz, hy, hu, ha, hb]
  by_cases h6 : i = b
  · rw [h6]; simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply, hx, hz, hy, hu, ha, hb]
  have hf : (swap u a * swap a b * (swap y z * swap x y)) i = i := by
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  simp [pow_succ, Perm.mul_apply, hf]

private theorem no_two_of_pow {g : Perm α} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hgp : g ^ p = 1)
    (hg : g ≠ 1) (k : ℕ) (hk : g ^ (2 ^ k) = 1) : False := by
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h3 : orderOf g ∣ Nat.gcd p (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hgp) (orderOf_dvd_of_pow_eq_one hk)
  rw [Nat.Coprime.gcd_eq_one hcop] at h3
  exact hg (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))

private theorem ne_one_of_apply {g : Perm α} {u s : α} (h : g u = s) (hus : s ≠ u) : g ≠ 1 := by
  rintro rfl
  rw [Perm.one_apply] at h
  exact hus h.symm

private theorem conj_three (τ : Perm α) (x y z : α) :
    τ * (swap x y * swap y z) * τ⁻¹ = swap (τ x) (τ y) * swap (τ y) (τ z) := by
  rw [swap_apply_apply, swap_apply_apply]
  group

private theorem pair_core (τ : Perm α) (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hwx : τ x ≠ x) (hwy : τ x ≠ y) (hwz : τ x ≠ z)
    (hk : ∃ k : ℕ, ((swap (τ x) (τ y) * swap (τ y) (τ z)) * (swap x y * swap y z)⁻¹) ^ (2 ^ k) = 1) :
    (τ y = x ∨ τ y = y ∨ τ y = z) ∧ (τ z = x ∨ τ z = y ∨ τ z = z) := by
  have hwa : τ x ≠ τ y := τ.injective.ne hxy
  have hwb : τ x ≠ τ z := τ.injective.ne hxz
  have hab : τ y ≠ τ z := τ.injective.ne hyz
  have hwx' := hwx.symm
  have hwy' := hwy.symm
  have hwz' := hwz.symm
  have hrot1 : swap x y * swap y z = swap z x * swap x y :=
    (rot3 x y z hxy hxz hyz).trans (rot3 y z x hyz hxy.symm hxz.symm)
  have hrot2 : swap (τ x) (τ y) * swap (τ y) (τ z) = swap (τ y) (τ z) * swap (τ z) (τ x) :=
    rot3 (τ x) (τ y) (τ z) hwa hwb hab
  obtain ⟨k, hk⟩ := hk
  by_cases hA : τ y = x ∨ τ y = y ∨ τ y = z
  · by_cases hB : τ z = x ∨ τ z = y ∨ τ z = z
    · exact ⟨hA, hB⟩
    exfalso
    push Not at hB
    obtain ⟨hB1, hB2, hB3⟩ := hB
    rcases hA with ha | ha | ha
    · rw [ha] at hk
      obtain ⟨hv, hu⟩ := five_pow x y z (τ x) (τ z) hxy hxz hwx' hB1.symm hyz hwy' hB2.symm
        hwz' hB3.symm hwb
      exact no_two_of_pow (p := 5) Nat.prime_five (by norm_num) hv (ne_one_of_apply hu hwx') k hk
    · rw [ha, rot3 x y z hxy hxz hyz] at hk
      obtain ⟨hv, hu⟩ := five_pow y z x (τ x) (τ z) hyz hxy.symm hwy' hB2.symm hxz.symm hwz'
        hB3.symm hwx' hB1.symm hwb
      exact no_two_of_pow (p := 5) Nat.prime_five (by norm_num) hv (ne_one_of_apply hu hwy') k hk
    · rw [ha, hrot1] at hk
      obtain ⟨hv, hu⟩ := five_pow z x y (τ x) (τ z) hxz.symm hyz.symm hwz' hB3.symm hxy hwx'
        hB1.symm hwy' hB2.symm hwb
      exact no_two_of_pow (p := 5) Nat.prime_five (by norm_num) hv (ne_one_of_apply hu hwz') k hk
  · exfalso
    push Not at hA
    obtain ⟨hA1, hA2, hA3⟩ := hA
    by_cases hB : τ z = x ∨ τ z = y ∨ τ z = z
    · rw [hrot2] at hk
      rcases hB with hb | hb | hb
      · rw [hb] at hk
        obtain ⟨hv, hu⟩ := five_pow x y z (τ y) (τ x) hxy hxz hA1.symm hwx' hyz hA2.symm hwy'
          hA3.symm hwz' hwa.symm
        exact no_two_of_pow (p := 5) Nat.prime_five (by norm_num) hv (ne_one_of_apply hu hA1.symm) k hk
      · rw [hb, rot3 x y z hxy hxz hyz] at hk
        obtain ⟨hv, hu⟩ := five_pow y z x (τ y) (τ x) hyz hxy.symm hA2.symm hwy' hxz.symm hA3.symm
          hwz' hA1.symm hwx' hwa.symm
        exact no_two_of_pow (p := 5) Nat.prime_five (by norm_num) hv (ne_one_of_apply hu hA2.symm) k hk
      · rw [hb, hrot1] at hk
        obtain ⟨hv, hu⟩ := five_pow z x y (τ y) (τ x) hxz.symm hyz.symm hA3.symm hwz' hxy hA1.symm
          hwx' hA2.symm hwy' hwa.symm
        exact no_two_of_pow (p := 5) Nat.prime_five (by norm_num) hv (ne_one_of_apply hu hA3.symm) k hk
    · push Not at hB
      obtain ⟨hB1, hB2, hB3⟩ := hB
      obtain ⟨hv, hu⟩ := disj_cube x y z (τ x) (τ y) (τ z) hxy hxz hyz hwa hwb hab hwx hwy hwz
        hA1 hA2 hA3 hB1 hB2 hB3
      exact no_two_of_pow (p := 3) Nat.prime_three (by norm_num) hv (ne_one_of_apply hu hwa.symm) k hk

private theorem step1_core (τ : Perm α) (Ω : Finset α) (hΩ : 4 ≤ Ω.card)
    (h2 : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ z ∈ Ω, x ≠ y → x ≠ z → y ≠ z →
      ∃ k : ℕ, ((τ * (swap x y * swap y z) * τ⁻¹) * (swap x y * swap y z)⁻¹) ^ (2 ^ k) = 1) :
    ∀ x ∈ Ω, τ x ∈ Ω := by
  intro x hx
  by_contra hwx
  have hne : ∀ p ∈ Ω, τ x ≠ p := fun p hp h => hwx (by rw [h]; exact hp)
  have hfix : ∀ y ∈ Ω, y ≠ x → τ y = y ∨ τ y = x := by
    intro y hy hyx
    have hcard : 1 < ((Ω.erase x).erase y).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hyx, hy⟩), Finset.card_erase_of_mem hx]
      omega
    obtain ⟨z, hz, z', hz', hzz'⟩ := Finset.one_lt_card.1 hcard
    simp only [Finset.mem_erase] at hz hz'
    obtain ⟨hzy, hzx, hzΩ⟩ := hz
    obtain ⟨hz'y, hz'x, hz'Ω⟩ := hz'
    obtain ⟨k, hk⟩ := h2 x hx y hy z hzΩ hyx.symm hzx.symm hzy.symm
    rw [conj_three] at hk
    have hA := pair_core τ x y z hyx.symm hzx.symm hzy.symm (hne x hx) (hne y hy) (hne z hzΩ)
      ⟨k, hk⟩
    obtain ⟨k', hk'⟩ := h2 x hx y hy z' hz'Ω hyx.symm hz'x.symm hz'y.symm
    rw [conj_three] at hk'
    have hA' := pair_core τ x y z' hyx.symm hz'x.symm hz'y.symm (hne x hx) (hne y hy)
      (hne z' hz'Ω) ⟨k', hk'⟩
    rcases hA.1 with h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · rcases hA'.1 with h' | h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
      · exact absurd (h.symm.trans h') hzz'
  have h3 : 2 < (Ω.erase x).card := by
    rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y1, hy1, y2, hy2, y3, hy3, h12, h13, h23⟩ := Finset.two_lt_card.1 h3
  rw [Finset.mem_erase] at hy1 hy2 hy3
  obtain ⟨hy1x, hy1Ω⟩ := hy1
  obtain ⟨hy2x, hy2Ω⟩ := hy2
  obtain ⟨hy3x, hy3Ω⟩ := hy3
  have key : ∃ y ∈ Ω, ∃ z ∈ Ω, y ≠ x ∧ z ≠ x ∧ y ≠ z ∧ τ y = y ∧ τ z = z := by
    rcases hfix y1 hy1Ω hy1x with e1 | e1 <;> rcases hfix y2 hy2Ω hy2x with e2 | e2 <;>
      rcases hfix y3 hy3Ω hy3x with e3 | e3
    all_goals first
      | exact ⟨y1, hy1Ω, y2, hy2Ω, hy1x, hy2x, h12, e1, e2⟩
      | exact ⟨y1, hy1Ω, y3, hy3Ω, hy1x, hy3x, h13, e1, e3⟩
      | exact ⟨y2, hy2Ω, y3, hy3Ω, hy2x, hy3x, h23, e2, e3⟩
      | exact absurd (τ.injective (e1.trans e2.symm)) h12
      | exact absurd (τ.injective (e1.trans e3.symm)) h13
      | exact absurd (τ.injective (e2.trans e3.symm)) h23
  obtain ⟨y, hy, z, hz, hyx, hzx, hyz, hty, htz⟩ := key
  obtain ⟨k, hk⟩ := h2 x hx y hy z hz hyx.symm hzx.symm hyz
  rw [conj_three, hty, htz] at hk
  obtain ⟨hcube, hval⟩ := four_cube x y z (τ x) hyx.symm hzx.symm (hne x hx).symm hyz
    (hne y hy).symm (hne z hz).symm
  exact no_two_of_pow (p := 3) Nat.prime_three (by norm_num) hcube (ne_one_of_apply hval (hne x hx)) k hk

private theorem perm_apply_inv_self' {β : Type} (f : Perm β) (x : β) : f (f⁻¹ x) = x := by simp

end I2013Aux

open I2013Aux Equiv

theorem i2013At_holds : I2013At := by

  intro Q _ N m e J hm5 _ hroot T hT hJT
  obtain ⟨⟨ψ⟩, hmov⟩ := hroot
  have hfin : (movedLettersOf e J).Finite := Set.toFinite _
  set Ω : Finset (Fin N) := hfin.toFinset with hΩdef
  have hΩcard : Ω.card = m := by
    rw [hΩdef, ← Set.ncard_eq_toFinset_card _ hfin]
    exact hmov
  have hσ : ∀ j ∈ J, ∀ i, i ∉ Ω → ((e j : alternatingGroup (Fin N)) : Perm (Fin N)) i = i := by
    intro j hj i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 (by exact ⟨j, hj, h⟩))
  have hcoe_gen : ∀ t j : Q, ((e (t * j * t⁻¹ * j⁻¹) : alternatingGroup (Fin N)) : Perm (Fin N)) =
      ((e t : alternatingGroup (Fin N)) : Perm (Fin N)) * ((e j : alternatingGroup (Fin N)) : Perm (Fin N))
        * ((e t : alternatingGroup (Fin N)) : Perm (Fin N))⁻¹
        * ((e j : alternatingGroup (Fin N)) : Perm (Fin N))⁻¹ := by
    intro t j
    simp [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hm5' : 5 ≤ Nat.card (Fin m) := by simp; omega
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup hm5'
  haveI : Nontrivial (alternatingGroup (Fin m)) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  haveI : Nontrivial ↥J := ψ.surjective.nontrivial
  haveI : IsSimpleGroup ↥J :=
    IsSimpleGroup.isSimpleGroup_of_surjective ψ.symm.toMonoidHom ψ.symm.surjective
  haveI : Nontrivial ↥Ω := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < Ω.card by rw [hΩcard]; omega)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hG : J.map e.toMonoidHom = (alternatingGroup.ofSubtype Ω).range := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨j, hj, rfl⟩
      rw [alternatingGroup.mem_range_ofSubtype_iff]
      intro i hi
      by_contra hiΩ
      exact (Equiv.Perm.mem_support.1 hi) (hσ j hj i hiΩ)
    · have h1 : Nat.card J = Nat.card (alternatingGroup (Fin m)) := Nat.card_congr ψ.toEquiv
      have hcardΩ : Nat.card ↥Ω = m := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, hΩcard]
      haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
      have hcardFin : Nat.card (Fin m) = m := by simp
      have h2 : Nat.card (alternatingGroup Ω) = Nat.card (alternatingGroup (Fin m)) := by
        rw [nat_card_alternatingGroup, nat_card_alternatingGroup,
          hcardΩ, hcardFin]
      have h3 : Nat.card (alternatingGroup Ω) = Nat.card (alternatingGroup.ofSubtype Ω).range :=
        Nat.card_congr (MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).toEquiv
      rw [← h3, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      exact (h2.trans h1.symm).le
  have hX : ∀ q : Q, (∀ i, i ∉ Ω → ((e q : alternatingGroup (Fin N)) : Perm (Fin N)) i = i) →
      q ∈ J := by
    intro q hq
    have hmem : e q ∈ (alternatingGroup.ofSubtype Ω).range := by
      rw [alternatingGroup.mem_range_ofSubtype_iff]
      intro i hi
      by_contra hiΩ
      exact (Equiv.Perm.mem_support.1 hi) (hq i hiΩ)
    rw [← hG] at hmem
    obtain ⟨j, hj, hjq⟩ := Subgroup.mem_map.1 hmem
    have : j = q := e.injective hjq
    exact this ▸ hj
  have hcyc : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ z ∈ Ω, x ≠ y → x ≠ z → y ≠ z →
      ∃ j ∈ J, ((e j : alternatingGroup (Fin N)) : Perm (Fin N)) = swap x y * swap y z := by
    intro x hx y hy z hz hxy hxz hyz
    have hmemA : swap x y * swap y z ∈ alternatingGroup (Fin N) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy,
        Equiv.Perm.sign_swap hyz]
      norm_num
    have hsupp : ((⟨swap x y * swap y z, hmemA⟩ : alternatingGroup (Fin N)) : Perm (Fin N)).support
        ⊆ Ω := by
      intro i hi
      by_contra hiΩ
      apply (Equiv.Perm.mem_support.1 hi)
      show (swap x y * swap y z) i = i
      have h1 : i ≠ x := fun h => hiΩ (h ▸ hx)
      have h2 : i ≠ y := fun h => hiΩ (h ▸ hy)
      have h3 : i ≠ z := fun h => hiΩ (h ▸ hz)
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne, h1, h2, h3]
    have hc : (⟨swap x y * swap y z, hmemA⟩ : alternatingGroup (Fin N)) ∈ J.map e.toMonoidHom := by
      rw [hG]; exact (alternatingGroup.mem_range_ofSubtype_iff Ω _).2 hsupp
    obtain ⟨j, hj, hjc⟩ := Subgroup.mem_map.1 hc
    exact ⟨j, hj, congrArg (fun g : alternatingGroup (Fin N) => (g : Perm (Fin N))) hjc⟩
  have hpowT : ∀ h : Q, h ∈ T →
      ∃ k : ℕ, ((e h : alternatingGroup (Fin N)) : Perm (Fin N)) ^ (2 ^ k) = 1 := by
    intro h hh
    obtain ⟨k, hk⟩ := hT ⟨h, hh⟩
    refine ⟨k, ?_⟩
    have h1 : h ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : e (h ^ (2 ^ k)) = 1 := by rw [h1, map_one]
    rw [map_pow] at h2
    have h3 := congrArg (fun g : alternatingGroup (Fin N) => (g : Perm (Fin N))) h2
    simpa using h3
  have hjT : ∀ j ∈ J, ∀ t ∈ T, j * t⁻¹ * j⁻¹ ∈ T := fun j hj t ht =>
    (Subgroup.mem_normalizer_iff.1 (hJT hj) t⁻¹).1 (T.inv_mem ht)
  have hcomm : ∀ j ∈ J, ∀ t ∈ T, t * j * t⁻¹ * j⁻¹ ∈ T := by
    intro j hj t ht
    simpa [mul_assoc] using T.mul_mem ht (hjT j hj t ht)
  have hstep : ∀ t ∈ T, ∀ x ∈ Ω, ((e t : alternatingGroup (Fin N)) : Perm (Fin N)) x ∈ Ω := by
    intro t ht
    refine step1_core ((e t : alternatingGroup (Fin N)) : Perm (Fin N)) Ω ?_ ?_
    · rw [hΩcard]; omega
    intro x hx y hy z hz hxy hxz hyz
    obtain ⟨j, hj, hej⟩ := hcyc x hx y hy z hz hxy hxz hyz
    obtain ⟨k, hk⟩ := hpowT _ (hcomm j hj t ht)
    refine ⟨k, ?_⟩
    rw [← hej]
    rw [hcoe_gen t j] at hk
    exact hk
  have hJT_bot : ∀ h : Q, h ∈ J → h ∈ T → h = 1 := by
    intro h hJh hTh
    have hK : (T.subgroupOf J).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 (hJT g.2) (n : Q)).1 hn⟩
    haveI := hK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf J) with hbot | htop
    · have hmem : (⟨h, hJh⟩ : ↥J) ∈ T.subgroupOf J := Subgroup.mem_subgroupOf.2 hTh
      rw [hbot, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
        Finset.two_lt_card.1 (show 2 < Ω.card by rw [hΩcard]; omega)
      obtain ⟨j0, hj0, hej0⟩ := hcyc x hx y hy z hz hxy hxz hyz
      have hmemK : (⟨j0, hj0⟩ : ↥J) ∈ T.subgroupOf J := by
        rw [htop]; exact Subgroup.mem_top _
      have hj0T : j0 ∈ T := Subgroup.mem_subgroupOf.1 hmemK
      obtain ⟨k, hk⟩ := hpowT j0 hj0T
      rw [hej0] at hk
      have hc3 : (swap x y * swap y z) ^ 3 = 1 := three_cube x y z hxy hxz hyz
      have hval : (swap x y * swap y z) x = y := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne, hxy, hxz]
      have hne : swap x y * swap y z ≠ 1 := ne_one_of_apply hval (Ne.symm hxy)
      exact no_two_of_pow Nat.prime_three (by norm_num) hc3 hne k hk
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have htT : t ∈ T := ht
  have hJm : t * j * t⁻¹ * j⁻¹ ∈ J := by
    apply hX
    intro i hi
    rw [hcoe_gen t j]
    have hσi : ((e j : alternatingGroup (Fin N)) : Perm (Fin N))⁻¹ i = i :=
      Equiv.Perm.inv_eq_iff_eq.2 (hσ j hj i hi).symm
    have hτi : ((e t : alternatingGroup (Fin N)) : Perm (Fin N))⁻¹ i ∉ Ω := fun hmem => hi (by
      have := hstep t htT _ hmem
      rwa [perm_apply_inv_self'] at this)
    have hσ' := hσ j hj _ hτi
    simp only [Perm.mul_apply, hσi, hσ', perm_apply_inv_self']
  have hone := hJT_bot _ hJm (hcomm j hj t htT)
  calc t * j = (t * j * t⁻¹ * j⁻¹) * (j * t) := by group
    _ = j * t := by rw [hone, one_mul]

end CFSG.LocalAnalysis.GLTheoremA
