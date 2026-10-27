module

public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.Certificates.PrimeCyclicRepresentatives

variable {P : Type*} [Group P] [LinearOrder P]

@[expose] def nonzeroPowers (p : ℕ) (x : P) : Finset P :=
  (Finset.Ico 1 p).image (x ^ ·)

theorem mem_nonzeroPowers_iff (p : ℕ) (x y : P) :
    y ∈ nonzeroPowers p x ↔ ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ x ^ j = y := by
  simp only [nonzeroPowers, Finset.mem_image, Finset.mem_Ico]
  aesop

theorem nonzeroPowers_nonempty (p : ℕ) (hp : p.Prime) (x : P) :
    (nonzeroPowers p x).Nonempty := by
  refine ⟨x, (mem_nonzeroPowers_iff p x x).mpr ⟨1, le_rfl, hp.one_lt, ?_⟩⟩
  exact pow_one x

@[expose] def minimum (p : ℕ) (hp : p.Prime) (x : P) : P :=
  (nonzeroPowers p x).min' (nonzeroPowers_nonempty p hp x)

theorem minimum_mem_nonzeroPowers (p : ℕ) (hp : p.Prime) (x : P) :
    minimum p hp x ∈ nonzeroPowers p x :=
  Finset.min'_mem _ _

theorem minimum_le (p : ℕ) (hp : p.Prime) (x : P) {y : P}
    (hy : y ∈ nonzeroPowers p x) : minimum p hp x ≤ y :=
  Finset.min'_le _ _ hy

omit [LinearOrder P] in
theorem orderOf_eq_prime_of_power (p : ℕ) (hp : p.Prime) {x : P}
    (hx : x ≠ 1) (hpow : x ^ p = 1) : orderOf x = p := by
  let : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hpow hx

theorem mem_nonzeroPowers_iff_mem_zpowers (p : ℕ) (hp : p.Prime)
    {x : P} (hx : x ≠ 1) (hpow : x ^ p = 1) (y : P) :
    y ∈ nonzeroPowers p x ↔ y ∈ Subgroup.zpowers x ∧ y ≠ 1 := by
  have horder := orderOf_eq_prime_of_power p hp hx hpow
  constructor
  · intro hy
    obtain ⟨j, hj, hjp, rfl⟩ := (mem_nonzeroPowers_iff p x y).mp hy
    refine ⟨Subgroup.npow_mem_zpowers x j, ?_⟩
    exact pow_ne_one_of_lt_orderOf (by omega) (by rwa [horder])
  · rintro ⟨hy, hy1⟩
    have hfin : IsOfFinOrder x := orderOf_pos_iff.mp (by rw [horder]; exact hp.pos)
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp
      ((hfin.mem_zpowers_iff_mem_range_orderOf).mp hy)
    have hjp : j < p := by simpa only [Finset.mem_range, horder] using hj
    have hj0 : j ≠ 0 := by
      intro he0
      subst j
      exact hy1 (by simpa using he.symm)
    exact (mem_nonzeroPowers_iff p x y).mpr ⟨j, by omega, hjp, he⟩

theorem orderOf_eq_prime_of_mem_nonzeroPowers (p : ℕ) (hp : p.Prime)
    {x y : P} (hx : x ≠ 1) (hpow : x ^ p = 1)
    (hy : y ∈ nonzeroPowers p x) : orderOf y = p := by
  obtain ⟨hygroup, hy1⟩ := (mem_nonzeroPowers_iff_mem_zpowers p hp hx hpow y).mp hy
  let : Fact p.Prime := ⟨hp⟩
  apply orderOf_eq_prime _ hy1
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [← orderOf_eq_prime_of_power p hp hx hpow]
  exact orderOf_dvd_of_mem_zpowers hygroup

theorem zpowers_eq_of_mem_nonzeroPowers (p : ℕ) (hp : p.Prime)
    {x y : P} (hx : x ≠ 1) (hpow : x ^ p = 1)
    (hy : y ∈ nonzeroPowers p x) : Subgroup.zpowers y = Subgroup.zpowers x := by
  have hygroup := ((mem_nonzeroPowers_iff_mem_zpowers p hp hx hpow y).mp hy).1
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime_of_power p hp hx hpow]
  have hcardy : Nat.card (Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime_of_mem_nonzeroPowers p hp hx hpow hy]
  let : Finite (Subgroup.zpowers x) :=
    Nat.finite_of_card_ne_zero (by rw [hcardx]; exact hp.ne_zero)
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hygroup)
    (by rw [hcardx, hcardy])

theorem orderOf_minimum (p : ℕ) (hp : p.Prime) {x : P}
    (hx : x ≠ 1) (hpow : x ^ p = 1) : orderOf (minimum p hp x) = p :=
  orderOf_eq_prime_of_mem_nonzeroPowers p hp hx hpow (minimum_mem_nonzeroPowers p hp x)

theorem zpowers_minimum (p : ℕ) (hp : p.Prime) {x : P}
    (hx : x ≠ 1) (hpow : x ^ p = 1) :
    Subgroup.zpowers (minimum p hp x) = Subgroup.zpowers x :=
  zpowers_eq_of_mem_nonzeroPowers p hp hx hpow (minimum_mem_nonzeroPowers p hp x)

theorem minimum_eq_iff_least (p : ℕ) (hp : p.Prime) {x : P}
    (hx : x ≠ 1) (hpow : x ^ p = 1) (r : P) :
    minimum p hp x = r ↔ r ∈ Subgroup.zpowers x ∧ r ≠ 1 ∧
      ∀ y ∈ Subgroup.zpowers x, y ≠ 1 → r ≤ y := by
  rw [minimum, Finset.min'_eq_iff]
  simp only [mem_nonzeroPowers_iff_mem_zpowers p hp hx hpow]
  aesop

theorem minimum_eq_of_zpowers_eq (p : ℕ) (hp : p.Prime) {x y : P}
    (hx : x ≠ 1) (hxp : x ^ p = 1) (hy : y ≠ 1) (hyp : y ^ p = 1)
    (hgroup : Subgroup.zpowers x = Subgroup.zpowers y) :
    minimum p hp x = minimum p hp y := by
  have hsets : nonzeroPowers p x = nonzeroPowers p y := by
    ext z
    rw [mem_nonzeroPowers_iff_mem_zpowers p hp hx hxp,
      mem_nonzeroPowers_iff_mem_zpowers p hp hy hyp, hgroup]
  unfold minimum
  congr 1

end CFSG.Certificates.PrimeCyclicRepresentatives
