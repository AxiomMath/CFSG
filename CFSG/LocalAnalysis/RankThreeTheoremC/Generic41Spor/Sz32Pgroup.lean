module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup
open scoped commutatorElement

section Abstract

variable {X : Type*} [Group X]

theorem szb_pow_mod25 {s : ℤ} (k : ℕ) :
    ∃ u : ℤ, (1 + 5 * s) ^ k = 1 + 5 * (s * k) + 25 * u := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨s ^ 2 * k + u * (1 + 5 * s), ?_⟩
    rw [pow_succ, hu]
    push_cast
    ring

theorem szb_pow_mod5 {n : ℤ} (h : n % 5 = 1) (k : ℕ) : n ^ k % 5 = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Int.mul_emod, ih, h]; norm_num

theorem szb_geom5 (r : ℤ) :
    ∑ l ∈ Finset.range 5, (1 + 5 * r) ^ l =
      5 + 25 * (2 * r + 10 * r ^ 2 + 25 * r ^ 3 + 25 * r ^ 4) := by
  simp [Finset.sum_range_succ]
  ring

theorem szb_S5 {μ : ℤ} (h : μ % 5 = 1) :
    ∃ E : ℤ, ∑ l ∈ Finset.range 5, μ ^ l = 5 + 25 * E := by
  obtain ⟨r, rfl⟩ : ∃ r : ℤ, μ = 1 + 5 * r := ⟨(μ - 1) / 5, by omega⟩
  exact ⟨_, szb_geom5 r⟩

theorem szb_exists_inv5 {p : ℤ} (hp : ¬ (5 : ℤ) ∣ p) : ∃ u w : ℤ, u * p = 1 + 5 * w := by
  have h : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases h with h | h | h | h
  · exact ⟨1, (p - 1) / 5, by omega⟩
  · exact ⟨3, (3 * p - 1) / 5, by omega⟩
  · exact ⟨2, (2 * p - 1) / 5, by omega⟩
  · exact ⟨4, (4 * p - 1) / 5, by omega⟩

theorem szb_dvd25 {s w e : ℤ} (hs : ¬ (5 : ℤ) ∣ s) :
    (25 : ℤ) ∣ 5 * s * w + 25 * e ↔ (5 : ℤ) ∣ w := by
  have hp : Prime (5 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_five
  rw [dvd_add_left (dvd_mul_right 25 e), show (25 : ℤ) = 5 * 5 by norm_num,
    mul_assoc, mul_dvd_mul_iff_left (by norm_num : (5 : ℤ) ≠ 0), hp.dvd_mul]
  constructor
  · rintro (h | h)
    · exact absurd h hs
    · exact h
  · exact Or.inr


theorem szb_zpowers_of_not_dvd {g : X} (hg : g ^ 5 = 1) {p : ℤ} (hp : ¬ (5 : ℤ) ∣ p) :
    g ∈ zpowers (g ^ p) := by
  obtain ⟨u, w, huw⟩ := szb_exists_inv5 hp
  have h5 : g ^ (5 * w) = 1 := by rw [zpow_mul]; simp [hg]
  have hg' : g = (g ^ p) ^ u := by
    rw [← zpow_mul, mul_comm p u, huw, zpow_add, zpow_one, h5, mul_one]
  have h := zpow_mem (mem_zpowers (g ^ p)) u
  rwa [← hg'] at h

structure SzbRel (a c y : X) (n ν : ℤ) : Prop where
  ac : a * c = c * a
  ya : y * a * y⁻¹ = a ^ n
  yc : y * c * y⁻¹ = c ^ ν
  y5 : y ^ 5 = 1
  inf : ∀ i j : ℤ, a ^ i = c ^ j → a ^ i = 1
  y_not : y ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c

theorem szb_y_zpow {y u : X} {m : ℤ} (h : y * u * y⁻¹ = u ^ m) (i : ℤ) :
    y * u ^ i = u ^ (m * i) * y := by
  rw [← mul_inv_eq_iff_eq_mul, ← conj_zpow, h, ← zpow_mul]

theorem szb_yk_zpow {y u : X} {m : ℤ} (h : y * u * y⁻¹ = u ^ m) (k : ℕ) (i : ℤ) :
    y ^ k * u ^ i = u ^ (m ^ k * i) * y ^ k := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    calc y ^ (k + 1) * u ^ i = y * (y ^ k * u ^ i) := by rw [pow_succ']; simp only [mul_assoc]
      _ = y * (u ^ (m ^ k * i) * y ^ k) := by rw [ih]
      _ = (y * u ^ (m ^ k * i)) * y ^ k := by simp only [mul_assoc]
      _ = (u ^ (m * (m ^ k * i)) * y) * y ^ k := by rw [szb_y_zpow h]
      _ = u ^ (m ^ (k + 1) * i) * y ^ (k + 1) := by
        rw [pow_succ' m k, pow_succ' y k]; simp only [mul_assoc]

theorem szb_mul {a c y : X} {n ν : ℤ} (R : SzbRel a c y n ν) (i j i' j' : ℤ) (k k' : ℕ) :
    (a ^ i * c ^ j * y ^ k) * (a ^ i' * c ^ j' * y ^ k') =
      a ^ (i + n ^ k * i') * c ^ (j + ν ^ k * j') * y ^ (k + k') := by
  have h1 := szb_yk_zpow R.ya k i'
  have h2 := szb_yk_zpow R.yc k j'
  have hac : Commute a c := R.ac
  have h3 : c ^ j * a ^ (n ^ k * i') = a ^ (n ^ k * i') * c ^ j :=
    ((hac.zpow_zpow (n ^ k * i') j).symm).eq
  calc (a ^ i * c ^ j * y ^ k) * (a ^ i' * c ^ j' * y ^ k')
      = a ^ i * c ^ j * (y ^ k * a ^ i') * c ^ j' * y ^ k' := by simp only [mul_assoc]
    _ = a ^ i * c ^ j * (a ^ (n ^ k * i') * y ^ k) * c ^ j' * y ^ k' := by rw [h1]
    _ = a ^ i * (c ^ j * a ^ (n ^ k * i')) * (y ^ k * c ^ j') * y ^ k' := by
        simp only [mul_assoc]
    _ = a ^ i * (a ^ (n ^ k * i') * c ^ j) * (c ^ (ν ^ k * j') * y ^ k) * y ^ k' := by
        rw [h2, h3]
    _ = a ^ (i + n ^ k * i') * c ^ (j + ν ^ k * j') * y ^ (k + k') := by
        rw [zpow_add, zpow_add, pow_add]; simp only [mul_assoc]

theorem szb_inv {a c y : X} {n ν : ℤ} (R : SzbRel a c y n ν) (i j : ℤ) (k : ℕ) :
    (a ^ i * c ^ j * y ^ k)⁻¹ =
      a ^ (-(n ^ (4 * k) * i)) * c ^ (-(ν ^ (4 * k) * j)) * y ^ (4 * k) := by
  have hy5k : y ^ (5 * k) = 1 := by rw [pow_mul, R.y5, one_pow]
  have ha : ∀ i : ℤ, a ^ (n ^ (5 * k) * i) = a ^ i := fun i => by
    have := szb_yk_zpow R.ya (5 * k) i
    rwa [hy5k, one_mul, mul_one, eq_comm] at this
  have hc : ∀ j : ℤ, c ^ (ν ^ (5 * k) * j) = c ^ j := fun j => by
    have := szb_yk_zpow R.yc (5 * k) j
    rwa [hy5k, one_mul, mul_one, eq_comm] at this
  rw [inv_eq_iff_mul_eq_one, szb_mul R]
  have e1 : i + n ^ k * -(n ^ (4 * k) * i) = i + -(n ^ (5 * k) * i) := by
    rw [show 5 * k = k + 4 * k by ring, pow_add]; ring
  have e2 : j + ν ^ k * -(ν ^ (4 * k) * j) = j + -(ν ^ (5 * k) * j) := by
    rw [show 5 * k = k + 4 * k by ring, pow_add]; ring
  rw [e1, e2, zpow_add, zpow_add, zpow_neg, zpow_neg, ha, hc, show k + 4 * k = 5 * k by ring,
    hy5k]
  simp

theorem szb_mem_Q {a c y : X} {n ν : ℤ} (R : SzbRel a c y n ν) {Q : Subgroup X}
    (hgen : Q = zpowers a ⊔ zpowers c ⊔ zpowers y) {q : X} :
    q ∈ Q ↔ ∃ (i j : ℤ) (k : ℕ), q = a ^ i * c ^ j * y ^ k := by
  constructor
  · intro hq
    let S : Subgroup X :=
      { carrier := {q | ∃ (i j : ℤ) (k : ℕ), q = a ^ i * c ^ j * y ^ k}
        mul_mem' := by
          rintro _ _ ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
          exact ⟨_, _, _, szb_mul R i j i' j' k k'⟩
        one_mem' := ⟨0, 0, 0, by simp⟩
        inv_mem' := by
          rintro _ ⟨i, j, k, rfl⟩
          exact ⟨_, _, _, szb_inv R i j k⟩ }
    have hle : Q ≤ S := by
      rw [hgen]
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [zpowers_le]; exact ⟨1, 0, 0, by simp⟩
      · rw [zpowers_le]; exact ⟨0, 1, 0, by simp⟩
      · rw [zpowers_le]; exact ⟨0, 0, 1, by simp⟩
    exact hle hq
  · rintro ⟨i, j, k, rfl⟩
    rw [hgen]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (zpow_mem_zpowers _ _)))
      (mem_sup_left (mem_sup_right (zpow_mem_zpowers _ _))))
      (mem_sup_right (pow_mem (mem_zpowers y) k))

theorem szb_nf_eq {a c y : X} {n ν : ℤ} (R : SzbRel a c y n ν) {i j i' j' : ℤ} {k k' : ℕ}
    (h : a ^ i * c ^ j * y ^ k = a ^ i' * c ^ j' * y ^ k') :
    (orderOf a : ℤ) ∣ i - i' ∧ (orderOf c : ℤ) ∣ j - j' ∧ (5 : ℤ) ∣ (k : ℤ) - k' := by
  have hu : a ^ i * c ^ j ∈ zpowers a ⊔ zpowers c :=
    mul_mem (mem_sup_left (zpow_mem_zpowers a i)) (mem_sup_right (zpow_mem_zpowers c j))
  have hu' : a ^ i' * c ^ j' ∈ zpowers a ⊔ zpowers c :=
    mul_mem (mem_sup_left (zpow_mem_zpowers a i')) (mem_sup_right (zpow_mem_zpowers c j'))
  have hy : y ^ ((k : ℤ) - k') = (a ^ i * c ^ j)⁻¹ * (a ^ i' * c ^ j') := by
    rw [zpow_sub, zpow_natCast, zpow_natCast]
    calc y ^ k * (y ^ k')⁻¹ = (a ^ i * c ^ j)⁻¹ * ((a ^ i * c ^ j) * y ^ k) * (y ^ k')⁻¹ := by
          group
      _ = (a ^ i * c ^ j)⁻¹ * ((a ^ i' * c ^ j') * y ^ k') * (y ^ k')⁻¹ := by rw [h]
      _ = (a ^ i * c ^ j)⁻¹ * (a ^ i' * c ^ j') := by group
  have h5 : (5 : ℤ) ∣ (k : ℤ) - k' := by
    by_contra hnd
    have h1 := szb_zpowers_of_not_dvd R.y5 hnd
    rw [hy] at h1
    exact R.y_not ((zpowers_le.2 (mul_mem (inv_mem hu) hu')) h1)
  have hy1 : y ^ ((k : ℤ) - k') = 1 := by
    obtain ⟨e, he⟩ := h5
    rw [he, zpow_mul]; simp [R.y5]
  rw [hy1, eq_comm, inv_mul_eq_one] at hy
  have hac : (a ^ i')⁻¹ * a ^ i = c ^ j' * (c ^ j)⁻¹ := by
    calc (a ^ i')⁻¹ * a ^ i = (a ^ i')⁻¹ * (a ^ i * c ^ j) * (c ^ j)⁻¹ := by group
      _ = (a ^ i')⁻¹ * (a ^ i' * c ^ j') * (c ^ j)⁻¹ := by rw [hy]
      _ = c ^ j' * (c ^ j)⁻¹ := by group
  have e1 : a ^ (i - i') = c ^ (j' - j) := by
    have e1 : (a ^ i')⁻¹ * a ^ i = a ^ (i - i') := by group
    have e2 : c ^ j' * (c ^ j)⁻¹ = c ^ (j' - j) := by group
    rw [← e1, ← e2]; exact hac
  have e0 := R.inf _ _ e1
  refine ⟨orderOf_dvd_iff_zpow_eq_one.2 e0, ?_, h5⟩
  have : c ^ (j' - j) = 1 := by rw [← e1]; exact e0
  exact (dvd_sub_comm).1 (orderOf_dvd_iff_zpow_eq_one.2 this)

theorem szb_nf_eq_of_dvd {a c y : X} {n ν : ℤ} (R : SzbRel a c y n ν) {i j i' j' : ℤ}
    {k k' : ℕ} (hi : (orderOf a : ℤ) ∣ i - i') (hj : (orderOf c : ℤ) ∣ j - j')
    (hk : (5 : ℤ) ∣ (k : ℤ) - k') :
    a ^ i * c ^ j * y ^ k = a ^ i' * c ^ j' * y ^ k' := by
  have e1 : a ^ i = a ^ i' := by
    have := orderOf_dvd_iff_zpow_eq_one.1 hi
    rwa [zpow_sub, mul_inv_eq_one] at this
  have e2 : c ^ j = c ^ j' := by
    have := orderOf_dvd_iff_zpow_eq_one.1 hj
    rwa [zpow_sub, mul_inv_eq_one] at this
  have e3 : y ^ k = y ^ k' := by
    obtain ⟨e, he⟩ := hk
    have : y ^ ((k : ℤ) - k') = 1 := by rw [he, zpow_mul]; simp [R.y5]
    rwa [zpow_sub, zpow_natCast, zpow_natCast, mul_inv_eq_one] at this
  rw [e1, e2, e3]

theorem szb_commute_iff {a c y : X} {n ν : ℤ} (R : SzbRel a c y n ν) (i j i' j' : ℤ)
    (k k' : ℕ) :
    (a ^ i * c ^ j * y ^ k) * (a ^ i' * c ^ j' * y ^ k') =
      (a ^ i' * c ^ j' * y ^ k') * (a ^ i * c ^ j * y ^ k) ↔
    ((orderOf a : ℤ) ∣ (n ^ k - 1) * i' - (n ^ k' - 1) * i ∧
      (orderOf c : ℤ) ∣ (ν ^ k - 1) * j' - (ν ^ k' - 1) * j) := by
  rw [szb_mul R, szb_mul R, add_comm k' k]
  constructor
  · intro h
    obtain ⟨h1, h2, -⟩ := szb_nf_eq R h
    refine ⟨?_, ?_⟩
    · convert h1 using 1; ring
    · convert h2 using 1; ring
  · rintro ⟨h1, h2⟩
    refine szb_nf_eq_of_dvd R ?_ ?_ (by simp)
    · convert h1 using 1; ring
    · convert h2 using 1; ring

theorem szb_pow_formula {a c y : X} {n ν : ℤ} (R : SzbRel a c y n ν) (i j : ℤ) (k l : ℕ) :
    (a ^ i * c ^ j * y ^ k) ^ l =
      a ^ (i * ∑ r ∈ Finset.range l, (n ^ k) ^ r) *
        c ^ (j * ∑ r ∈ Finset.range l, (ν ^ k) ^ r) * y ^ (k * l) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have e1 : i * ∑ r ∈ Finset.range l, (n ^ k) ^ r + n ^ (k * l) * i =
        i * ∑ r ∈ Finset.range (l + 1), (n ^ k) ^ r := by
      rw [Finset.sum_range_succ, pow_mul]; ring
    have e2 : j * ∑ r ∈ Finset.range l, (ν ^ k) ^ r + ν ^ (k * l) * j =
        j * ∑ r ∈ Finset.range (l + 1), (ν ^ k) ^ r := by
      rw [Finset.sum_range_succ, pow_mul]; ring
    rw [pow_succ, ih, szb_mul R, e1, e2, show k * l + k = k * (l + 1) by ring]

theorem szb_pow5 {a c y : X} {n ν : ℤ} (R : SzbRel a c y n ν) (hn : n % 5 = 1)
    (hν : ν % 5 = 1) (i j : ℤ) (k : ℕ) :
    ∃ E₁ E₂ : ℤ, (a ^ i * c ^ j * y ^ k) ^ 5 =
      a ^ (i * (5 + 25 * E₁)) * c ^ (j * (5 + 25 * E₂)) := by
  obtain ⟨E₁, h1⟩ := szb_S5 (szb_pow_mod5 hn k)
  obtain ⟨E₂, h2⟩ := szb_S5 (szb_pow_mod5 hν k)
  refine ⟨E₁, E₂, ?_⟩
  rw [szb_pow_formula R, h1, h2, mul_comm k 5, pow_mul, R.y5, one_pow, mul_one]

theorem szb_central_of_gens {Q : Subgroup X} {a c y z : X}
    (hgen : Q = zpowers a ⊔ zpowers c ⊔ zpowers y)
    (ha : z * a = a * z) (hc : z * c = c * z) (hy : z * y = y * z) :
    ∀ q ∈ Q, q * z = z * q := by
  have hle : Q ≤ Subgroup.centralizer {z} := by
    rw [hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [zpowers_le, mem_centralizer_iff]
      intro h hh; rw [Set.mem_singleton_iff.1 hh]; exact ha
    · rw [zpowers_le, mem_centralizer_iff]
      intro h hh; rw [Set.mem_singleton_iff.1 hh]; exact hc
    · rw [zpowers_le, mem_centralizer_iff]
      intro h hh; rw [Set.mem_singleton_iff.1 hh]; exact hy
  intro q hq
  have := mem_centralizer_iff.1 (hle hq) z (Set.mem_singleton z)
  exact this.symm

theorem szb_central_pow5 {a c y : X} {n ν s : ℤ} (R : SzbRel a c y n ν) (hoa : orderOf a = 25)
    (hn : n = 1 + 5 * s) (hs : ¬ (5 : ℤ) ∣ s) (hν : ν % 5 = 1) {Q : Subgroup X}
    (hgen : Q = zpowers a ⊔ zpowers c ⊔ zpowers y) {z : X} (hzQ : z ∈ Q)
    (hz : z * y = y * z) : ∃ j : ℤ, z ^ 5 = c ^ j := by
  obtain ⟨i, j, k, rfl⟩ := (szb_mem_Q R hgen).1 hzQ
  have hn5 : n % 5 = 1 := by omega
  have hcomm := (szb_commute_iff R i j 0 0 k 1).1 (by simpa using hz)
  have h1 := hcomm.1
  rw [hoa] at h1
  have h2 : (25 : ℤ) ∣ 5 * s * i + 25 * 0 := by
    have : (n ^ k - 1) * 0 - (n ^ 1 - 1) * i = -(5 * s * i) := by rw [hn]; ring
    rw [this] at h1
    simpa using h1
  have hi : (5 : ℤ) ∣ i := (szb_dvd25 hs).1 h2
  obtain ⟨E₁, E₂, h5⟩ := szb_pow5 R hn5 hν i j k
  refine ⟨j * (5 + 25 * E₂), ?_⟩
  rw [h5]
  have : a ^ (i * (5 + 25 * E₁)) = 1 := by
    obtain ⟨i₀, rfl⟩ := hi
    have : (5 * i₀) * (5 + 25 * E₁) = 25 * (i₀ * (1 + 5 * E₁)) := by ring
    rw [this, zpow_mul]
    have h25 : a ^ (25 : ℤ) = 1 := by
      have := pow_orderOf_eq_one a
      rw [hoa] at this
      simpa using this
    rw [h25, one_zpow]
  rw [this, one_mul]

theorem szb_rel_of_pres {Q : Subgroup X} {a c y x : X} (hQ : Sz32QPres Q a c y x) {n ν : ℤ}
    (hn : y * a * y⁻¹ = a ^ n) (hν : y * c * y⁻¹ = c ^ ν) : SzbRel a c y n ν where
  ac := hQ.ac
  ya := hn
  yc := hν
  y5 := hQ.y5
  inf := fun i j h => by
    have hm : a ^ i ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c :=
      ⟨zpow_mem_zpowers a i, h ▸ zpow_mem_zpowers c j⟩
    rw [hQ.inf] at hm
    exact Subgroup.mem_bot.1 hm
  y_not := hQ.y_not

theorem szb_conj_zpow {y u : X} {m : ℤ} (h : y * u * y⁻¹ = u ^ m) (i : ℤ) :
    y * u ^ i * y⁻¹ = u ^ (m * i) := by
  rw [← conj_zpow, h, ← zpow_mul]

theorem szb_swap_data {Q : Subgroup X} {a x g : X} (hg : g ∈ Subgroup.normalizer (Q : Set X))
    (ha : a ∈ Q)
    (hswap : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (a ^ 5)) :
    ∃ (w : X) (r : ℤ), w ∈ Q ∧ w ^ 5 = x ∧ g * x * g⁻¹ = (a ^ 5) ^ r := by
  have hx : g * x * g⁻¹ ∈ Subgroup.zpowers (a ^ 5) := by
    rw [← hswap]
    exact ⟨x, mem_zpowers x, by simp [MulAut.conj_apply]⟩
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine ⟨g⁻¹ * a ^ r * g, r, ?_, ?_, hr.symm⟩
  · exact (Subgroup.mem_normalizer_iff''.1 hg (a ^ r)).1 (zpow_mem ha r)
  · have e1 : (g⁻¹ * a ^ r * g) ^ 5 = g⁻¹ * (a ^ r) ^ 5 * g := by
      simpa [inv_inv] using conj_pow (a := g⁻¹) (b := a ^ r) (i := 5)
    have e2 : (a ^ r) ^ 5 = (a ^ 5) ^ r := by
      rw [← zpow_natCast (a ^ r) 5, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [e1, e2, hr]
    group

theorem szb_swap_m {a c y x w : X} {n ν : ℤ} {m : ℕ} (R : SzbRel a c y n ν) (hn5 : n % 5 = 1)
    (hν5 : ν % 5 = 1) {Q : Subgroup X} (hgen : Q = zpowers a ⊔ zpowers c ⊔ zpowers y)
    (hwQ : w ∈ Q) (hw : w ^ 5 = x) (hx : x ∈ zpowers c) (hxo : orderOf x = 5)
    (hoc : orderOf c = 5 ^ m) (hm1 : 1 ≤ m) : 2 ≤ m := by
  obtain ⟨i, j, k, rfl⟩ := (szb_mem_Q R hgen).1 hwQ
  obtain ⟨E₁, E₂, h5⟩ := szb_pow5 R hn5 hν5 i j k
  rw [h5] at hw
  obtain ⟨p, hp⟩ := mem_zpowers_iff.1 hx
  have h1 : a ^ (i * (5 + 25 * E₁)) = c ^ (p - j * (5 + 25 * E₂)) := by
    rw [zpow_sub, hp, ← hw, mul_inv_cancel_right]
  have h0 := R.inf _ _ h1
  rw [h0, one_mul] at hw
  by_contra hlt
  have hm : m = 1 := by omega
  subst hm
  have hc5 : c ^ 5 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hoc] at this
  have : x = 1 := by
    rw [← hw, show j * (5 + 25 * E₂) = 5 * (j * (1 + 5 * E₂)) by ring, zpow_mul]
    simp [hc5]
  rw [this, orderOf_one] at hxo
  omega

theorem szb_swap_t {Q : Subgroup X} {a c y x g : X} {n ν s t : ℤ} {m : ℕ}
    (R : SzbRel a c y n ν) (hgen : Q = zpowers a ⊔ zpowers c ⊔ zpowers y)
    (hoa : orderOf a = 25) (hoc : orderOf c = 5 ^ m) (hm2 : 2 ≤ m)
    (hn : n = 1 + 5 * s) (hs : ¬ (5 : ℤ) ∣ s) (hν : ν = 1 + 5 * t)
    (hy : y ∈ Q) (hxo : orderOf x = 5) (hx : x ∈ zpowers c)
    (hg : g ∈ Subgroup.normalizer (Q : Set X)) (r : ℤ) (hr : g * x * g⁻¹ = (a ^ 5) ^ r) :
    ¬ (5 : ℤ) ∣ t := by
  intro ht
  obtain ⟨t₀, rfl⟩ := ht
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hν5 : ν % 5 = 1 := by omega
  have hn5 : n % 5 = 1 := by omega
  have hc25 : c ^ (25 * 5 ^ m') = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hoc, show 5 ^ (m' + 2) = 25 * 5 ^ m' by ring] at this
  obtain ⟨p, hp⟩ := mem_zpowers_iff.1 hx
  have hx5 : x ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo] at this
  have hcp : c ^ (p * 5) = 1 := by
    have h : c ^ (p * 5) = x ^ 5 := by
      rw [← hp, ← zpow_natCast (c ^ p) 5, ← zpow_mul]; norm_cast
    rw [h, hx5]
  obtain ⟨d, hd⟩ : (25 * (5 ^ m' : ℤ)) ∣ p * 5 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 hcp
    rw [hoc] at this
    have e : (((5 ^ (m' + 2) : ℕ)) : ℤ) = 25 * (5 ^ m' : ℤ) := by push_cast; ring
    rwa [e] at this
  have hpd : p = 5 * 5 ^ m' * d := by linarith
  set z₁ : X := c ^ ((5 ^ m' : ℤ) * d) with hz₁
  have hxz : z₁ ^ 5 = x := by
    rw [hz₁, ← hp, ← zpow_natCast, ← zpow_mul, hpd]
    congr 1
    push_cast; ring
  have hz₁a : z₁ * a = a * z₁ := by
    have : Commute a c := R.ac
    exact ((this.zpow_right _).symm).eq
  have hz₁c : z₁ * c = c * z₁ := ((Commute.refl c).zpow_left _).eq
  have hz₁y : z₁ * y = y * z₁ := by
    have h1 : y * z₁ * y⁻¹ = c ^ (ν * ((5 ^ m' : ℤ) * d)) := szb_conj_zpow R.yc _
    have h2 : ν * ((5 ^ m' : ℤ) * d) = (5 ^ m' : ℤ) * d + (25 * 5 ^ m') * (t₀ * d) := by
      rw [hν]; ring
    have h3 : c ^ (ν * ((5 ^ m' : ℤ) * d)) = z₁ := by
      rw [h2, zpow_add, ← hz₁, zpow_mul]
      have : c ^ ((25 * 5 ^ m' : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hc25
      push_cast at this
      rw [this, one_zpow, mul_one]
    rw [h3] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hz₁Q : ∀ q ∈ Q, q * z₁ = z₁ * q := szb_central_of_gens hgen hz₁a hz₁c hz₁y
  have hz₁mem : z₁ ∈ Q := by
    rw [hgen]
    exact mem_sup_left (mem_sup_right (zpow_mem_zpowers c _))
  set z₂ : X := g * z₁ * g⁻¹ with hz₂
  have hz₂Q : z₂ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg z₁).1 hz₁mem
  have hz₂y : z₂ * y = y * z₂ := by
    have hy' : g⁻¹ * y * g ∈ Q := (Subgroup.mem_normalizer_iff''.1 hg y).1 hy
    have := hz₁Q _ hy'
    calc z₂ * y = g * z₁ * (g⁻¹ * y * g) * g⁻¹ := by rw [hz₂]; group
      _ = g * ((g⁻¹ * y * g) * z₁) * g⁻¹ := by rw [this]; group
      _ = y * z₂ := by rw [hz₂]; group
  have hz₂5 : z₂ ^ 5 = (a ^ 5) ^ r := by
    rw [hz₂, conj_pow, hxz, hr]
  obtain ⟨j, hj⟩ := szb_central_pow5 R hoa hn hs hν5 hgen hz₂Q hz₂y
  rw [hz₂5] at hj
  have e : a ^ (5 * r) = (a ^ 5) ^ r := by rw [zpow_mul]; simp
  have h1 : a ^ (5 * r) = 1 := R.inf _ _ (e.trans hj)
  have h2 : g * x * g⁻¹ = 1 := by rw [hr, ← e]; exact h1
  have hx1 : x = 1 := by simpa using h2
  rw [hx1, orderOf_one] at hxo
  omega

theorem szb_swap_m_le {a c y : X} {n ν t : ℤ} {m : ℕ} (R : SzbRel a c y n ν)
    (hoc : orderOf c = 5 ^ m) (hν : ν = 1 + 5 * t) (ht : ¬ (5 : ℤ) ∣ t) : m ≤ 2 := by
  by_contra hlt
  have hlt : 2 < m := not_le.1 hlt
  have h1 : c ^ (ν ^ 5 - 1) = 1 := by
    have := szb_yk_zpow R.yc 5 1
    rw [R.y5, one_mul, mul_one, mul_one, zpow_one] at this
    rw [zpow_sub, zpow_one, ← this, mul_inv_cancel]
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hoc] at h2
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
  have h3 : (125 : ℤ) ∣ ν ^ 5 - 1 := by
    refine Dvd.dvd.trans ?_ h2
    exact ⟨5 ^ m', by push_cast; ring⟩
  have key : ν ^ 5 - 1 =
      25 * (t + 5 * (2 * t ^ 2 + 10 * t ^ 3 + 25 * t ^ 4 + 25 * t ^ 5)) := by
    rw [hν]; ring
  rw [key] at h3
  have h4 : (5 : ℤ) ∣ t + 5 * (2 * t ^ 2 + 10 * t ^ 3 + 25 * t ^ 4 + 25 * t ^ 5) := by
    have : (25 * 5 : ℤ) ∣ 25 * (t + 5 * (2 * t ^ 2 + 10 * t ^ 3 + 25 * t ^ 4 + 25 * t ^ 5)) := by
      simpa using h3
    exact (mul_dvd_mul_iff_left (by norm_num : (25 : ℤ) ≠ 0)).1 this
  generalize (2 * t ^ 2 + 10 * t ^ 3 + 25 * t ^ 4 + 25 * t ^ 5) = F at h4
  omega

theorem sz32_pgroup_swap {Q : Subgroup X} {a c y x g : X} (hQ : Sz32QPres Q a c y x)
    (hg : g ∈ Subgroup.normalizer (Q : Set X))
    (hswap : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (a ^ 5)) :
    orderOf c = 25 ∧ y * c * y⁻¹ ≠ c := by
  obtain ⟨m, hm1, hoc⟩ := hQ.ord_c
  obtain ⟨n, hya, hn5, hn25⟩ := hQ.ya
  obtain ⟨ν, hyc, hν5⟩ := hQ.yc
  have R := szb_rel_of_pres hQ hya hyc
  obtain ⟨s, hn, hs⟩ : ∃ s : ℤ, n = 1 + 5 * s ∧ ¬ (5 : ℤ) ∣ s :=
    ⟨(n - 1) / 5, by omega, by omega⟩
  obtain ⟨t, hν⟩ : ∃ t : ℤ, ν = 1 + 5 * t := ⟨(ν - 1) / 5, by omega⟩
  obtain ⟨w, r, hwQ, hw, hr⟩ := szb_swap_data hg hQ.a_mem hswap
  have hm2 := szb_swap_m R hn5 hν5 hQ.gen hwQ hw hQ.x_mem hQ.x_ord hoc hm1
  have ht := szb_swap_t R hQ.gen hQ.ord_a hoc hm2 hn hs hν hQ.y_mem hQ.x_ord hQ.x_mem hg r hr
  have hm := szb_swap_m_le R hoc hν ht
  have hm' : m = 2 := le_antisymm hm hm2
  subst hm'
  refine ⟨by rw [hoc]; norm_num, ?_⟩
  intro hcy
  have h1 : c ^ ν = c := by rw [← hyc]; exact hcy
  have h2 : c ^ (ν - 1) = 1 := by rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
  have h3 := orderOf_dvd_iff_zpow_eq_one.2 h2
  rw [hoc] at h3
  apply ht
  rw [hν] at h3
  push_cast at h3
  omega

structure SzbB2 (Q : Subgroup X) (a c y : X) (s t : ℤ) : Prop where
  rel : SzbRel a c y (1 + 5 * s) (1 + 5 * t)
  gen : Q = zpowers a ⊔ zpowers c ⊔ zpowers y
  oa : orderOf a = 25
  oc : orderOf c = 25
  hs : ¬ (5 : ℤ) ∣ s
  ht : ¬ (5 : ℤ) ∣ t

theorem szb_b2_of_pres {Q : Subgroup X} {a c y x : X} (hQ : Sz32QPres Q a c y x)
    (hc : orderOf c = 25) (hyc : y * c * y⁻¹ ≠ c) : ∃ s t : ℤ, SzbB2 Q a c y s t := by
  obtain ⟨n, hya, hn5, hn25⟩ := hQ.ya
  obtain ⟨ν, hyc', hν5⟩ := hQ.yc
  obtain ⟨s, hn, hs⟩ : ∃ s : ℤ, n = 1 + 5 * s ∧ ¬ (5 : ℤ) ∣ s :=
    ⟨(n - 1) / 5, by omega, by omega⟩
  obtain ⟨t, hν⟩ : ∃ t : ℤ, ν = 1 + 5 * t := ⟨(ν - 1) / 5, by omega⟩
  refine ⟨s, t, ?_⟩
  have R := szb_rel_of_pres hQ hya hyc'
  rw [hn, hν] at R
  refine ⟨R, hQ.gen, hQ.ord_a, hc, hs, ?_⟩
  rintro ⟨t₀, rfl⟩
  apply hyc
  rw [hyc', hν]
  have h25 : c ^ (25 : ℤ) = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc] at this
    simpa using this
  have : c ^ (1 + 5 * (5 * t₀)) = c := by
    rw [show 1 + 5 * (5 * t₀) = 1 + 25 * t₀ by ring, zpow_add, zpow_one, zpow_mul, h25, one_zpow,
      mul_one]
  exact this

theorem szb_b2_nf_eq_iff {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t)
    {i j i' j' : ℤ} {k k' : ℕ} :
    a ^ i * c ^ j * y ^ k = a ^ i' * c ^ j' * y ^ k' ↔
      ((25 : ℤ) ∣ i - i' ∧ (25 : ℤ) ∣ j - j' ∧ (5 : ℤ) ∣ (k : ℤ) - k') := by
  constructor
  · intro h
    have := szb_nf_eq H.rel h
    rw [H.oa, H.oc] at this
    simpa using this
  · rintro ⟨h1, h2, h3⟩
    exact szb_nf_eq_of_dvd H.rel (by rw [H.oa]; simpa using h1) (by rw [H.oc]; simpa using h2) h3

theorem szb_b2_commute {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t)
    (i j i' j' : ℤ) (k k' : ℕ) :
    (a ^ i * c ^ j * y ^ k) * (a ^ i' * c ^ j' * y ^ k') =
      (a ^ i' * c ^ j' * y ^ k') * (a ^ i * c ^ j * y ^ k) ↔
    ((5 : ℤ) ∣ k * i' - k' * i ∧ (5 : ℤ) ∣ k * j' - k' * j) := by
  rw [szb_commute_iff H.rel, H.oa, H.oc]
  obtain ⟨u, hu⟩ := szb_pow_mod25 (s := s) k
  obtain ⟨u', hu'⟩ := szb_pow_mod25 (s := s) k'
  obtain ⟨v, hv⟩ := szb_pow_mod25 (s := t) k
  obtain ⟨v', hv'⟩ := szb_pow_mod25 (s := t) k'
  have e1 : ((1 + 5 * s) ^ k - 1) * i' - ((1 + 5 * s) ^ k' - 1) * i =
      5 * s * (k * i' - k' * i) + 25 * (u * i' - u' * i) := by rw [hu, hu']; ring
  have e2 : ((1 + 5 * t) ^ k - 1) * j' - ((1 + 5 * t) ^ k' - 1) * j =
      5 * t * (k * j' - k' * j) + 25 * (v * j' - v' * j) := by rw [hv, hv']; ring
  rw [e1, e2]
  push_cast
  rw [szb_dvd25 H.hs, szb_dvd25 H.ht]

theorem szb_b2_pow5 {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t)
    (i j : ℤ) (k : ℕ) : (a ^ i * c ^ j * y ^ k) ^ 5 = a ^ (5 * i) * c ^ (5 * j) := by
  obtain ⟨E₁, E₂, h⟩ := szb_pow5 H.rel (by omega) (by omega) i j k
  rw [h]
  have := (szb_b2_nf_eq_iff H (i := i * (5 + 25 * E₁)) (j := j * (5 + 25 * E₂)) (i' := 5 * i)
    (j' := 5 * j) (k := 0) (k' := 0)).2 ⟨⟨i * E₁, by ring⟩, ⟨j * E₂, by ring⟩, by simp⟩
  simpa using this

theorem szb_mem_sup_zpowers {Hs : Subgroup X} {g : X} (hH : ∀ h ∈ Hs, h * g = g * h) {w : X} :
    w ∈ Hs ⊔ zpowers g ↔ ∃ h ∈ Hs, ∃ r : ℤ, w = h * g ^ r := by
  constructor
  · intro hw
    let S : Subgroup X :=
      { carrier := {w | ∃ h ∈ Hs, ∃ r : ℤ, w = h * g ^ r}
        mul_mem' := by
          rintro _ _ ⟨h₁, hh₁, r₁, rfl⟩ ⟨h₂, hh₂, r₂, rfl⟩
          refine ⟨h₁ * h₂, mul_mem hh₁ hh₂, r₁ + r₂, ?_⟩
          have hc : Commute h₂ g := hH h₂ hh₂
          have hc' : g ^ r₁ * h₂ = h₂ * g ^ r₁ := (hc.zpow_right r₁).symm.eq
          calc h₁ * g ^ r₁ * (h₂ * g ^ r₂) = h₁ * (g ^ r₁ * h₂) * g ^ r₂ := by
                simp only [mul_assoc]
            _ = h₁ * h₂ * g ^ (r₁ + r₂) := by rw [hc', zpow_add]; simp only [mul_assoc]
        one_mem' := ⟨1, one_mem _, 0, by simp⟩
        inv_mem' := by
          rintro _ ⟨h, hh, r, rfl⟩
          refine ⟨h⁻¹, inv_mem hh, -r, ?_⟩
          have hc : Commute h⁻¹ g := hH h⁻¹ (inv_mem hh)
          have hc' : g ^ (-r) * h⁻¹ = h⁻¹ * g ^ (-r) := (hc.zpow_right (-r)).symm.eq
          rw [mul_inv_rev, ← zpow_neg, hc'] }
    have hle : Hs ⊔ zpowers g ≤ S := by
      refine sup_le ?_ ?_
      · intro h hh; exact ⟨h, hh, 0, by simp⟩
      · rw [zpowers_le]; exact ⟨1, one_mem _, 1, by simp⟩
    exact hle hw
  · rintro ⟨h, hh, r, rfl⟩
    exact mul_mem_sup hh (zpow_mem_zpowers g r)

theorem szb_zpow_nat {y : X} (hy5 : y ^ 5 = 1) (r : ℤ) : ∃ k : ℕ, y ^ r = y ^ k := by
  refine ⟨(r % 5).toNat, ?_⟩
  have h : ((r % 5).toNat : ℤ) = r % 5 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  rw [← zpow_natCast, h]
  conv_lhs => rw [← Int.emod_add_mul_ediv r 5]
  rw [zpow_add, zpow_mul]
  simp [hy5]

theorem szb_pow5_zpow (g : X) (i : ℤ) : (g ^ 5) ^ i = g ^ (5 * i) := by
  rw [zpow_mul]; simp

theorem szb_b2_mem_Z {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) {z : X} :
    z ∈ sz32Z a c ↔ ∃ i j : ℤ, z = a ^ (5 * i) * c ^ (5 * j) := by
  have hcomm : ∀ h ∈ zpowers (a ^ 5), h * c ^ 5 = c ^ 5 * h := by
    intro h hh
    obtain ⟨r, rfl⟩ := mem_zpowers_iff.1 hh
    have hac : Commute a c := H.rel.ac
    exact ((hac.pow_pow 5 5).zpow_left r).eq
  unfold sz32Z
  rw [szb_mem_sup_zpowers hcomm]
  constructor
  · rintro ⟨h, hh, r, rfl⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hh
    exact ⟨i, r, by rw [szb_pow5_zpow, szb_pow5_zpow]⟩
  · rintro ⟨i, j, rfl⟩
    exact ⟨(a ^ 5) ^ i, zpow_mem_zpowers _ _, j, by rw [szb_pow5_zpow, szb_pow5_zpow]⟩

theorem szb_b2_mem_Q0 {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) {q : X} :
    q ∈ sz32Q0 a c ↔ ∃ i j : ℤ, q = a ^ i * c ^ j := by
  have hcomm : ∀ h ∈ zpowers a, h * c = c * h := by
    intro h hh
    obtain ⟨r, rfl⟩ := mem_zpowers_iff.1 hh
    have hac : Commute a c := H.rel.ac
    exact (hac.zpow_left r).eq
  unfold sz32Q0
  rw [szb_mem_sup_zpowers hcomm]
  constructor
  · rintro ⟨h, hh, r, rfl⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hh
    exact ⟨i, r, rfl⟩
  · rintro ⟨i, j, rfl⟩
    exact ⟨a ^ i, zpow_mem_zpowers _ _, j, rfl⟩

theorem szb_b2_mem_Om {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) {w : X} :
    w ∈ sz32Om a c y ↔ ∃ (i j : ℤ) (k : ℕ), w = a ^ (5 * i) * c ^ (5 * j) * y ^ k := by
  have hcomm : ∀ h ∈ sz32Z a c, h * y = y * h := by
    intro h hh
    obtain ⟨i, j, rfl⟩ := (szb_b2_mem_Z H).1 hh
    have := (szb_b2_commute H (5 * i) (5 * j) 0 0 0 1).2
      ⟨⟨-i, by push_cast; ring⟩, ⟨-j, by push_cast; ring⟩⟩
    simpa using this
  unfold sz32Om
  rw [szb_mem_sup_zpowers hcomm]
  constructor
  · rintro ⟨h, hh, r, rfl⟩
    obtain ⟨i, j, rfl⟩ := (szb_b2_mem_Z H).1 hh
    obtain ⟨k, hk⟩ := szb_zpow_nat H.rel.y5 r
    exact ⟨i, j, k, by rw [hk]⟩
  · rintro ⟨i, j, k, rfl⟩
    refine ⟨a ^ (5 * i) * c ^ (5 * j), (szb_b2_mem_Z H).2 ⟨i, j, rfl⟩, k, ?_⟩
    simp

theorem szb_zmod_eq {N : ℕ} [NeZero N] {u v : ZMod N} (h : (N : ℤ) ∣ (u.val : ℤ) - v.val) :
    u = v := by
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub (v.val : ℤ) (u.val : ℤ) N).2 h
  simpa using this.symm

theorem szb_card_param {T : Subgroup X} {α : Type*} (f : α → X) (hf : Function.Injective f)
    (hT : ∀ q, q ∈ T ↔ ∃ p, f p = q) : Nat.card T = Nat.card α := by
  have h : (T : Set X) = Set.range f := by
    ext q; simpa using hT q
  rw [← Nat.card_range_of_injective hf, ← h]
  rfl

theorem szb_b2_cast {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) (i j : ℤ)
    (k : ℕ) :
    a ^ (((i : ZMod 25).val : ℕ) : ℤ) * c ^ (((j : ZMod 25).val : ℕ) : ℤ) *
        y ^ ((k : ZMod 5).val) = a ^ i * c ^ j * y ^ k := by
  refine (szb_b2_nf_eq_iff H).2 ⟨?_, ?_, ?_⟩
  · rw [ZMod.val_intCast]; push_cast; omega
  · rw [ZMod.val_intCast]; push_cast; omega
  · rw [ZMod.val_natCast]; push_cast; omega

theorem szb_b2_cast5 {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) (i j : ℤ)
    (k : ℕ) :
    a ^ (5 * (((i : ZMod 5).val : ℕ) : ℤ)) * c ^ (5 * (((j : ZMod 5).val : ℕ) : ℤ)) *
        y ^ ((k : ZMod 5).val) = a ^ (5 * i) * c ^ (5 * j) * y ^ k := by
  refine (szb_b2_nf_eq_iff H).2 ⟨?_, ?_, ?_⟩
  · rw [ZMod.val_intCast]; push_cast; omega
  · rw [ZMod.val_intCast]; push_cast; omega
  · rw [ZMod.val_natCast]; push_cast; omega

theorem szb_b2_card_Q {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    Nat.card Q = 5 ^ 5 := by
  let f : ZMod 25 × ZMod 25 × ZMod 5 → X := fun p =>
    a ^ ((p.1.val : ℕ) : ℤ) * c ^ ((p.2.1.val : ℕ) : ℤ) * y ^ p.2.2.val
  have hf : Function.Injective f := by
    intro p p' h
    obtain ⟨h1, h2, h3⟩ := (szb_b2_nf_eq_iff H).1 h
    exact Prod.ext (szb_zmod_eq (by exact_mod_cast h1))
      (Prod.ext (szb_zmod_eq (by exact_mod_cast h2)) (szb_zmod_eq (by exact_mod_cast h3)))
  have hT : ∀ q, q ∈ Q ↔ ∃ p, f p = q := by
    intro q
    rw [szb_mem_Q H.rel H.gen]
    constructor
    · rintro ⟨i, j, k, rfl⟩
      exact ⟨((i : ZMod 25), (j : ZMod 25), (k : ZMod 5)), szb_b2_cast H i j k⟩
    · rintro ⟨p, rfl⟩
      exact ⟨_, _, _, rfl⟩
  rw [szb_card_param f hf hT]
  simp [Nat.card_prod, Nat.card_zmod]

theorem szb_b2_cast0 {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) (i j : ℤ) :
    a ^ (((i : ZMod 25).val : ℕ) : ℤ) * c ^ (((j : ZMod 25).val : ℕ) : ℤ) = a ^ i * c ^ j := by
  simpa using szb_b2_cast H i j 0

theorem szb_b2_cast50 {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t)
    (i j : ℤ) :
    a ^ (5 * (((i : ZMod 5).val : ℕ) : ℤ)) * c ^ (5 * (((j : ZMod 5).val : ℕ) : ℤ)) =
      a ^ (5 * i) * c ^ (5 * j) := by
  simpa using szb_b2_cast5 H i j 0

theorem szb_b2_card_Q0 {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    Nat.card (sz32Q0 a c) = 5 ^ 4 := by
  let f : ZMod 25 × ZMod 25 → X := fun p =>
    a ^ ((p.1.val : ℕ) : ℤ) * c ^ ((p.2.val : ℕ) : ℤ)
  have hf : Function.Injective f := by
    intro p p' h
    have h' : a ^ ((p.1.val : ℕ) : ℤ) * c ^ ((p.2.val : ℕ) : ℤ) * y ^ 0 =
        a ^ ((p'.1.val : ℕ) : ℤ) * c ^ ((p'.2.val : ℕ) : ℤ) * y ^ 0 := by
      rw [pow_zero, mul_one, mul_one]; exact h
    obtain ⟨h1, h2, -⟩ := (szb_b2_nf_eq_iff H).1 h'
    exact Prod.ext (szb_zmod_eq (by exact_mod_cast h1)) (szb_zmod_eq (by exact_mod_cast h2))
  have hT : ∀ q, q ∈ sz32Q0 a c ↔ ∃ p, f p = q := by
    intro q
    rw [szb_b2_mem_Q0 H]
    constructor
    · rintro ⟨i, j, rfl⟩
      exact ⟨((i : ZMod 25), (j : ZMod 25)), szb_b2_cast0 H i j⟩
    · rintro ⟨p, rfl⟩
      exact ⟨_, _, rfl⟩
  rw [szb_card_param f hf hT]
  simp [Nat.card_prod, Nat.card_zmod]

theorem szb_b2_card_Z {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    Nat.card (sz32Z a c) = 5 ^ 2 := by
  let f : ZMod 5 × ZMod 5 → X := fun p =>
    a ^ (5 * ((p.1.val : ℕ) : ℤ)) * c ^ (5 * ((p.2.val : ℕ) : ℤ))
  have hf : Function.Injective f := by
    intro p p' h
    have h' : a ^ (5 * ((p.1.val : ℕ) : ℤ)) * c ^ (5 * ((p.2.val : ℕ) : ℤ)) * y ^ 0 =
        a ^ (5 * ((p'.1.val : ℕ) : ℤ)) * c ^ (5 * ((p'.2.val : ℕ) : ℤ)) * y ^ 0 := by
      rw [pow_zero, mul_one, mul_one]; exact h
    obtain ⟨h1, h2, -⟩ := (szb_b2_nf_eq_iff H).1 h'
    refine Prod.ext (szb_zmod_eq ?_) (szb_zmod_eq ?_)
    · push_cast; omega
    · push_cast; omega
  have hT : ∀ q, q ∈ sz32Z a c ↔ ∃ p, f p = q := by
    intro q
    rw [szb_b2_mem_Z H]
    constructor
    · rintro ⟨i, j, rfl⟩
      exact ⟨((i : ZMod 5), (j : ZMod 5)), szb_b2_cast50 H i j⟩
    · rintro ⟨p, rfl⟩
      exact ⟨_, _, rfl⟩
  rw [szb_card_param f hf hT]
  simp [Nat.card_prod, Nat.card_zmod]

theorem szb_b2_card_Om {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    Nat.card (sz32Om a c y) = 5 ^ 3 := by
  let f : ZMod 5 × ZMod 5 × ZMod 5 → X := fun p =>
    a ^ (5 * ((p.1.val : ℕ) : ℤ)) * c ^ (5 * ((p.2.1.val : ℕ) : ℤ)) * y ^ p.2.2.val
  have hf : Function.Injective f := by
    intro p p' h
    obtain ⟨h1, h2, h3⟩ := (szb_b2_nf_eq_iff H).1 h
    refine Prod.ext (szb_zmod_eq ?_) (Prod.ext (szb_zmod_eq ?_) (szb_zmod_eq ?_))
    · push_cast; omega
    · push_cast; omega
    · exact_mod_cast h3
  have hT : ∀ q, q ∈ sz32Om a c y ↔ ∃ p, f p = q := by
    intro q
    rw [szb_b2_mem_Om H]
    constructor
    · rintro ⟨i, j, k, rfl⟩
      exact ⟨((i : ZMod 5), (j : ZMod 5), (k : ZMod 5)), szb_b2_cast5 H i j k⟩
    · rintro ⟨p, rfl⟩
      exact ⟨_, _, _, rfl⟩
  rw [szb_card_param f hf hT]
  simp [Nat.card_prod, Nat.card_zmod]

theorem szb_dvd5_mul {k i : ℤ} (hk : ¬ (5 : ℤ) ∣ k) (h : (5 : ℤ) ∣ k * i) : (5 : ℤ) ∣ i := by
  have hp : Prime (5 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_five
  rcases hp.dvd_mul.1 h with h | h
  · exact absurd h hk
  · exact h

theorem szb_x_eq {c x : X} (hoc : orderOf c = 25) (hx : x ∈ zpowers c) (hxo : orderOf x = 5) :
    zpowers x = zpowers (c ^ 5) := by
  have hc25 : c ^ (25 : ℕ) = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hoc] at this
  obtain ⟨p, hp⟩ := mem_zpowers_iff.1 hx
  have hx5 : x ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo] at this
  have hcp : c ^ (p * 5) = 1 := by
    have h : c ^ (p * 5) = x ^ 5 := by
      rw [← hp, ← zpow_natCast (c ^ p) 5, ← zpow_mul]; norm_cast
    rw [h, hx5]
  have hd := orderOf_dvd_iff_zpow_eq_one.2 hcp
  rw [hoc] at hd
  obtain ⟨p₁, rfl⟩ : (5 : ℤ) ∣ p := by push_cast at hd; omega
  have hxp : x = (c ^ 5) ^ p₁ := by rw [← hp, szb_pow5_zpow]
  have hne : ¬ (5 : ℤ) ∣ p₁ := by
    rintro ⟨q, rfl⟩
    have : x = 1 := by
      rw [hxp, szb_pow5_zpow, show 5 * (5 * q) = 25 * q by ring, zpow_mul]
      simp [hc25]
    rw [this, orderOf_one] at hxo
    omega
  have hg5 : (c ^ 5) ^ 5 = 1 := by rw [← pow_mul]; exact hc25
  apply le_antisymm
  · rw [zpowers_le, hxp]; exact zpow_mem (mem_zpowers _) _
  · rw [zpowers_le]
    have := szb_zpowers_of_not_dvd hg5 hne
    rwa [← hxp] at this

theorem szb_b2_a_mem {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) : a ∈ Q := by
  rw [H.gen]; exact mem_sup_left (mem_sup_left (mem_zpowers a))

theorem szb_b2_c_mem {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) : c ∈ Q := by
  rw [H.gen]; exact mem_sup_left (mem_sup_right (mem_zpowers c))

theorem szb_b2_y_mem {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) : y ∈ Q := by
  rw [H.gen]; exact mem_sup_right (mem_zpowers y)

theorem szb_b2_Q0_mul_comm {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t)
    {u v : X} (hu : u ∈ sz32Q0 a c) (hv : v ∈ sz32Q0 a c) : u * v = v * u := by
  obtain ⟨i, j, rfl⟩ := (szb_b2_mem_Q0 H).1 hu
  obtain ⟨i', j', rfl⟩ := (szb_b2_mem_Q0 H).1 hv
  have h := (szb_b2_commute H i j i' j' 0 0).2 ⟨by simp, by simp⟩
  simpa using h

theorem szb_b2_Q0_comm {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    IsMulCommutative (sz32Q0 a c) :=
  isMulCommutative_iff.2 fun u v => Subtype.ext (szb_b2_Q0_mul_comm H u.2 v.2)

theorem szb_b2_Z_le_Q0 {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    sz32Z a c ≤ sz32Q0 a c := by
  intro z hz
  obtain ⟨i, j, rfl⟩ := (szb_b2_mem_Z H).1 hz
  exact (szb_b2_mem_Q0 H).2 ⟨5 * i, 5 * j, rfl⟩

theorem szb_b2_Z_le_Q {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    sz32Z a c ≤ Q := by
  intro z hz
  obtain ⟨i, j, rfl⟩ := (szb_b2_mem_Z H).1 hz
  exact mul_mem (zpow_mem (szb_b2_a_mem H) _) (zpow_mem (szb_b2_c_mem H) _)

theorem szb_b2_center {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) ↔ z ∈ sz32Z a c := by
  intro z hz
  obtain ⟨i, j, k, rfl⟩ := (szb_mem_Q H.rel H.gen).1 hz
  constructor
  · intro hc
    have h1 := (szb_b2_commute H i j 1 0 k 0).1 (by simpa using (hc a (szb_b2_a_mem H)).symm)
    have h2 := (szb_b2_commute H i j 0 0 k 1).1 (by simpa using (hc y (szb_b2_y_mem H)).symm)
    have hk : (5 : ℤ) ∣ (k : ℤ) := by simpa using h1.1
    have hi : (5 : ℤ) ∣ i := by simpa using h2.1
    have hj : (5 : ℤ) ∣ j := by simpa using h2.2
    obtain ⟨i₀, rfl⟩ := hi
    obtain ⟨j₀, rfl⟩ := hj
    refine (szb_b2_mem_Z H).2 ⟨i₀, j₀, ?_⟩
    have := (szb_b2_nf_eq_iff H (i := 5 * i₀) (j := 5 * j₀) (i' := 5 * i₀) (j' := 5 * j₀)
      (k := k) (k' := 0)).2 ⟨by simp, by simp, by simpa using hk⟩
    simpa using this
  · intro hzZ q hq
    obtain ⟨i₀, j₀, hz0⟩ := (szb_b2_mem_Z H).1 hzZ
    have hz1 : a ^ i * c ^ j * y ^ k = a ^ (5 * i₀) * c ^ (5 * j₀) * y ^ 0 := by
      rw [pow_zero, mul_one]; exact hz0
    obtain ⟨d1, d2, d3⟩ := (szb_b2_nf_eq_iff H).1 hz1
    have hk : (5 : ℤ) ∣ (k : ℤ) := by simpa using d3
    have hi : (5 : ℤ) ∣ i := by omega
    have hj : (5 : ℤ) ∣ j := by omega
    obtain ⟨i', j', k', rfl⟩ := (szb_mem_Q H.rel H.gen).1 hq
    refine ((szb_b2_commute H i j i' j' k k').2 ⟨?_, ?_⟩).symm
    · exact dvd_sub (Dvd.dvd.mul_right hk i') (Dvd.dvd.mul_left hi _)
    · exact dvd_sub (Dvd.dvd.mul_right hk j') (Dvd.dvd.mul_left hj _)

theorem szb_comm_aux {a c y : X} (hac : a * c = c * a) (A B A' B' : ℤ) (s : ℕ) :
    a ^ A * c ^ B * y ^ s * (a ^ A' * c ^ B' * y ^ s)⁻¹ = a ^ (A - A') * c ^ (B - B') := by
  have h1 : a ^ A * c ^ B * y ^ s * (a ^ A' * c ^ B' * y ^ s)⁻¹ =
      a ^ A * c ^ B * (c ^ B')⁻¹ * (a ^ A')⁻¹ := by group
  have hc : Commute a c := hac
  have h2 : c ^ (B - B') * a ^ (-A') = a ^ (-A') * c ^ (B - B') :=
    ((hc.zpow_zpow (-A') (B - B')).eq).symm
  calc a ^ A * c ^ B * y ^ s * (a ^ A' * c ^ B' * y ^ s)⁻¹
      = a ^ A * c ^ B * (c ^ B')⁻¹ * (a ^ A')⁻¹ := h1
    _ = a ^ A * (c ^ (B - B') * a ^ (-A')) := by
        rw [zpow_sub, zpow_neg]; simp only [mul_assoc]
    _ = a ^ A * (a ^ (-A') * c ^ (B - B')) := by rw [h2]
    _ = a ^ (A - A') * c ^ (B - B') := by
        have : a ^ (A - A') = a ^ A * a ^ (-A') := by rw [sub_eq_add_neg, zpow_add]
        rw [this]; simp only [mul_assoc]

theorem szb_comm_formula {a c y : X} {n ν : ℤ} (R : SzbRel a c y n ν) (i j i' j' : ℤ)
    (k k' : ℕ) :
    ⁅a ^ i * c ^ j * y ^ k, a ^ i' * c ^ j' * y ^ k'⁆ =
      a ^ ((n ^ k - 1) * i' - (n ^ k' - 1) * i) *
        c ^ ((ν ^ k - 1) * j' - (ν ^ k' - 1) * j) := by
  rw [commutatorElement_def]
  have e : ∀ g₁ g₂ : X, g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = (g₁ * g₂) * (g₂ * g₁)⁻¹ :=
    fun g₁ g₂ => by group
  rw [e, szb_mul R i j i' j' k k', szb_mul R i' j' i j k' k, add_comm k' k,
    szb_comm_aux R.ac]
  have e1 : i + n ^ k * i' - (i' + n ^ k' * i) = (n ^ k - 1) * i' - (n ^ k' - 1) * i := by ring
  have e2 : j + ν ^ k * j' - (j' + ν ^ k' * j) = (ν ^ k - 1) * j' - (ν ^ k' - 1) * j := by ring
  rw [e1, e2]

theorem szb_b2_pow5_one {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t)
    (i j : ℤ) (k : ℕ) (hi : (5 : ℤ) ∣ i) (hj : (5 : ℤ) ∣ j) :
    (a ^ i * c ^ j * y ^ k) ^ 5 = 1 := by
  rw [szb_b2_pow5 H]
  have := (szb_b2_nf_eq_iff H (i := 5 * i) (j := 5 * j) (i' := 0) (j' := 0) (k := 0)
    (k' := 0)).2 ⟨by omega, by omega, by simp⟩
  simpa using this

theorem szb_b2_comm_eq {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    ⁅Q, Q⁆ = sz32Z a c := by
  apply le_antisymm
  · rw [commutator_le]
    intro g₁ h₁ g₂ h₂
    obtain ⟨i, j, k, rfl⟩ := (szb_mem_Q H.rel H.gen).1 h₁
    obtain ⟨i', j', k', rfl⟩ := (szb_mem_Q H.rel H.gen).1 h₂
    rw [szb_comm_formula H.rel]
    obtain ⟨u, hu⟩ := szb_pow_mod25 (s := s) k
    obtain ⟨u', hu'⟩ := szb_pow_mod25 (s := s) k'
    obtain ⟨v, hv⟩ := szb_pow_mod25 (s := t) k
    obtain ⟨v', hv'⟩ := szb_pow_mod25 (s := t) k'
    have e1 : ((1 + 5 * s) ^ k - 1) * i' - ((1 + 5 * s) ^ k' - 1) * i =
        5 * (s * k * i' + 5 * u * i' - s * k' * i - 5 * u' * i) := by rw [hu, hu']; ring
    have e2 : ((1 + 5 * t) ^ k - 1) * j' - ((1 + 5 * t) ^ k' - 1) * j =
        5 * (t * k * j' + 5 * v * j' - t * k' * j - 5 * v' * j) := by rw [hv, hv']; ring
    rw [e1, e2]
    exact (szb_b2_mem_Z H).2 ⟨_, _, rfl⟩
  · have hy := szb_b2_y_mem H
    have ha := szb_b2_a_mem H
    have hc := szb_b2_c_mem H
    have h1 : ⁅y, a⁆ = a ^ (5 * s) := by
      rw [commutatorElement_def, H.rel.ya]; group
    have h2 : ⁅y, c⁆ = c ^ (5 * t) := by
      rw [commutatorElement_def, H.rel.yc]; group
    have ha25 : (a ^ 5) ^ 5 = 1 := by
      rw [← pow_mul]
      have := pow_orderOf_eq_one a
      rwa [H.oa] at this
    have hc25 : (c ^ 5) ^ 5 = 1 := by
      rw [← pow_mul]
      have := pow_orderOf_eq_one c
      rwa [H.oc] at this
    have ma : a ^ (5 * s) ∈ ⁅Q, Q⁆ := h1 ▸ commutator_mem_commutator hy ha
    have mc : c ^ (5 * t) ∈ ⁅Q, Q⁆ := h2 ▸ commutator_mem_commutator hy hc
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      have := szb_zpowers_of_not_dvd ha25 H.hs
      rw [szb_pow5_zpow] at this
      exact (zpowers_le.2 ma) this
    · rw [zpowers_le]
      have := szb_zpowers_of_not_dvd hc25 H.ht
      rw [szb_pow5_zpow] at this
      exact (zpowers_le.2 mc) this

theorem szb_b2_pow5_mem {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    ∀ v ∈ Q, v ^ 5 ∈ sz32Z a c := by
  intro v hv
  obtain ⟨i, j, k, rfl⟩ := (szb_mem_Q H.rel H.gen).1 hv
  rw [szb_b2_pow5 H]
  exact (szb_b2_mem_Z H).2 ⟨i, j, rfl⟩

theorem szb_b2_pow5_surj {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    ∀ z ∈ sz32Z a c, ∃ v ∈ Q, v ^ 5 = z := by
  intro z hz
  obtain ⟨i, j, rfl⟩ := (szb_b2_mem_Z H).1 hz
  refine ⟨a ^ i * c ^ j * y ^ 0, (szb_mem_Q H.rel H.gen).2 ⟨i, j, 0, rfl⟩, ?_⟩
  rw [szb_b2_pow5 H]

theorem szb_b2_exp {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    ∀ v ∈ Q, v ^ 25 = 1 := by
  intro v hv
  obtain ⟨i, j, k, rfl⟩ := (szb_mem_Q H.rel H.gen).1 hv
  rw [show (25 : ℕ) = 5 * 5 by norm_num, pow_mul, szb_b2_pow5 H]
  have := szb_b2_pow5_one H (5 * i) (5 * j) 0 ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa using this

theorem szb_b2_Z_elem {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    IsElemAbelian 5 (sz32Z a c) := by
  unfold IsElemAbelian
  refine ⟨isMulCommutative_iff.2 fun u v => Subtype.ext
    (szb_b2_Q0_mul_comm H (szb_b2_Z_le_Q0 H u.2) (szb_b2_Z_le_Q0 H v.2)), ?_⟩
  intro x hx
  obtain ⟨i, j, rfl⟩ := (szb_b2_mem_Z H).1 hx
  have := szb_b2_pow5_one H (5 * i) (5 * j) 0 ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa using this

theorem szb_b2_Om_le {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    sz32Om a c y ≤ Q :=
  sup_le (szb_b2_Z_le_Q H) (zpowers_le.2 (szb_b2_y_mem H))

theorem szb_b2_Om_elem {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    IsElemAbelian 5 (sz32Om a c y) := by
  unfold IsElemAbelian
  refine ⟨isMulCommutative_iff.2 ?_, ?_⟩
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨i, j, k, rfl⟩ := (szb_b2_mem_Om H).1 hu
    obtain ⟨i', j', k', rfl⟩ := (szb_b2_mem_Om H).1 hv
    apply Subtype.ext
    exact (szb_b2_commute H (5 * i) (5 * j) (5 * i') (5 * j') k k').2
      ⟨⟨k * i' - k' * i, by ring⟩, ⟨k * j' - k' * j, by ring⟩⟩
  · intro x hx
    obtain ⟨i, j, k, rfl⟩ := (szb_b2_mem_Om H).1 hx
    exact szb_b2_pow5_one H (5 * i) (5 * j) k ⟨i, rfl⟩ ⟨j, rfl⟩

theorem szb_b2_Om_all {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    ∀ v ∈ Q, v ^ 5 = 1 → v ∈ sz32Om a c y := by
  intro v hv hv5
  obtain ⟨i, j, k, rfl⟩ := (szb_mem_Q H.rel H.gen).1 hv
  rw [szb_b2_pow5 H] at hv5
  obtain ⟨h1, h2, -⟩ := (szb_b2_nf_eq_iff H (k := 0) (k' := 0) (i := 5 * i) (j := 5 * j)
    (i' := 0) (j' := 0)).1 (by simpa using hv5)
  obtain ⟨i₀, rfl⟩ : (5 : ℤ) ∣ i := by omega
  obtain ⟨j₀, rfl⟩ : (5 : ℤ) ∣ j := by omega
  exact (szb_b2_mem_Om H).2 ⟨i₀, j₀, k, rfl⟩

theorem szb_b2_Om_k {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) {i j : ℤ}
    {k : ℕ} (h : a ^ (5 * i) * c ^ (5 * j) * y ^ k ∉ sz32Z a c) : ¬ (5 : ℤ) ∣ (k : ℤ) := by
  intro hk
  apply h
  refine (szb_b2_mem_Z H).2 ⟨i, j, ?_⟩
  have := (szb_b2_nf_eq_iff H (i := 5 * i) (j := 5 * j) (i' := 5 * i) (j' := 5 * j) (k := k)
    (k' := 0)).2 ⟨by simp, by simp, by simpa using hk⟩
  simpa using this

theorem szb_b2_cent_le {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    ∀ u ∈ sz32Om a c y, u ∉ sz32Z a c → ∀ q ∈ Q, q * u = u * q → q ∈ sz32Om a c y := by
  intro u hu huZ q hq hqu
  obtain ⟨i, j, k, rfl⟩ := (szb_b2_mem_Om H).1 hu
  have hk := szb_b2_Om_k H huZ
  obtain ⟨i', j', k', rfl⟩ := (szb_mem_Q H.rel H.gen).1 hq
  obtain ⟨h1, h2⟩ := (szb_b2_commute H i' j' (5 * i) (5 * j) k' k).1 hqu
  have h1' : (5 : ℤ) ∣ (k : ℤ) * i' :=
    (dvd_sub_right (show (5 : ℤ) ∣ (k' : ℤ) * (5 * i) from ⟨k' * i, by ring⟩)).1 h1
  have h2' : (5 : ℤ) ∣ (k : ℤ) * j' :=
    (dvd_sub_right (show (5 : ℤ) ∣ (k' : ℤ) * (5 * j) from ⟨k' * j, by ring⟩)).1 h2
  obtain ⟨i₀, rfl⟩ := szb_dvd5_mul hk h1'
  obtain ⟨j₀, rfl⟩ := szb_dvd5_mul hk h2'
  exact (szb_b2_mem_Om H).2 ⟨i₀, j₀, k', rfl⟩

theorem szb_exists_solve {s k p : ℤ} (h : ¬ (5 : ℤ) ∣ s * k) :
    ∃ α W : ℤ, p + s * k * α = 5 * W := by
  obtain ⟨u, w, huw⟩ := szb_exists_inv5 h
  exact ⟨-(p * u), -(p * w), by linear_combination (-p) * huw⟩

theorem szb_b2_shear {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t) :
    ∀ u ∈ sz32Om a c y, u ∉ sz32Z a c → ∀ z ∈ sz32Z a c,
      ∃ q ∈ Q, q * u * q⁻¹ = u * z := by
  intro u hu huZ z hz
  obtain ⟨i, j, k, rfl⟩ := (szb_b2_mem_Om H).1 hu
  have hk := szb_b2_Om_k H huZ
  obtain ⟨p, r, rfl⟩ := (szb_b2_mem_Z H).1 hz
  have hp : Prime (5 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_five
  have hsk : ¬ (5 : ℤ) ∣ s * k := fun h => (hp.dvd_mul.1 h).elim H.hs hk
  have htk : ¬ (5 : ℤ) ∣ t * k := fun h => (hp.dvd_mul.1 h).elim H.ht hk
  obtain ⟨α, Wα, hα⟩ := szb_exists_solve (p := p) hsk
  obtain ⟨β, Wβ, hβ⟩ := szb_exists_solve (p := r) htk
  obtain ⟨u₁, hu₁⟩ := szb_pow_mod25 (s := s) k
  obtain ⟨v₁, hv₁⟩ := szb_pow_mod25 (s := t) k
  refine ⟨a ^ α * c ^ β, (szb_mem_Q H.rel H.gen).2 ⟨α, β, 0, by simp⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  have e1 : a ^ α * c ^ β * (a ^ (5 * i) * c ^ (5 * j) * y ^ k) =
      a ^ (α + 5 * i) * c ^ (β + 5 * j) * y ^ k := by
    simpa using szb_mul H.rel α β (5 * i) (5 * j) 0 k
  have e2 : a ^ (5 * p) * c ^ (5 * r) * (a ^ α * c ^ β) =
      a ^ (5 * p + α) * c ^ (5 * r + β) := by
    simpa using szb_mul H.rel (5 * p) (5 * r) α β 0 0
  have e3 : a ^ (5 * i) * c ^ (5 * j) * y ^ k * (a ^ (5 * p + α) * c ^ (5 * r + β)) =
      a ^ (5 * i + (1 + 5 * s) ^ k * (5 * p + α)) *
        c ^ (5 * j + (1 + 5 * t) ^ k * (5 * r + β)) * y ^ k := by
    simpa using szb_mul H.rel (5 * i) (5 * j) (5 * p + α) (5 * r + β) k 0
  rw [e1, mul_assoc (a ^ (5 * i) * c ^ (5 * j) * y ^ k), e2, e3]
  refine (szb_b2_nf_eq_iff H).2 ⟨?_, ?_, by simp⟩
  · exact ⟨-(Wα + s * k * p + u₁ * (5 * p + α)), by rw [hu₁]; linear_combination (-5) * hα⟩
  · exact ⟨-(Wβ + t * k * r + v₁ * (5 * r + β)), by rw [hv₁]; linear_combination (-5) * hβ⟩

theorem szb_exists_l {k : ℤ} (k' : ℤ) (hk : ¬ (5 : ℤ) ∣ k) :
    ∃ l : ℕ, l < 5 ∧ (5 : ℤ) ∣ k' + k * l := by
  obtain ⟨u, w, huw⟩ := szb_exists_inv5 hk
  have hl := Int.emod_add_mul_ediv (-(k' * u)) 5
  have h0 : 0 ≤ (-(k' * u)) % 5 := Int.emod_nonneg _ (by norm_num)
  have h5 : (-(k' * u)) % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  refine ⟨((-(k' * u)) % 5).toNat, by omega, ?_⟩
  have hc : (((-(k' * u)) % 5).toNat : ℤ) = (-(k' * u)) % 5 := Int.toNat_of_nonneg h0
  rw [hc]
  exact ⟨-(k' * w) - k * ((-(k' * u)) / 5), by linear_combination k * hl - k' * huw⟩

theorem szb_comm_of_isMulComm {B : Subgroup X} (hB : IsMulCommutative B) {u v : X} (hu : u ∈ B)
    (hv : v ∈ B) : u * v = v * u := by
  haveI := hB
  exact congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : B) ⟨v, hv⟩)

theorem szb_b2_Q0_unique {Q : Subgroup X} {a c y : X} {s t : ℤ} (H : SzbB2 Q a c y s t)
    (B : Subgroup X) (hBQ : B ≤ Q) (hB : IsMulCommutative B) (hcard : 5 ^ 4 ≤ Nat.card B) :
    B = sz32Q0 a c := by
  have hfin0 : Finite (sz32Q0 a c) :=
    Nat.finite_of_card_ne_zero (by rw [szb_b2_card_Q0 H]; norm_num)
  have hfinZ : Finite (sz32Z a c) :=
    Nat.finite_of_card_ne_zero (by rw [szb_b2_card_Z H]; norm_num)
  have hle : B ≤ sz32Q0 a c := by
    intro b hb
    by_contra hbQ0
    obtain ⟨i, j, k, rfl⟩ := (szb_mem_Q H.rel H.gen).1 (hBQ hb)
    have hk : ¬ (5 : ℤ) ∣ (k : ℤ) := by
      intro hk
      apply hbQ0
      refine (szb_b2_mem_Q0 H).2 ⟨i, j, ?_⟩
      have := (szb_b2_nf_eq_iff H (i := i) (j := j) (i' := i) (j' := j) (k := k)
        (k' := 0)).2 ⟨by simp, by simp, by simpa using hk⟩
      simpa using this
    have hcover : ∀ β ∈ B, ∃ z ∈ sz32Z a c, ∃ l : Fin 5,
        β = z * ((a ^ i * c ^ j * y ^ k) ^ (l : ℕ))⁻¹ := by
      intro β hβ
      obtain ⟨i', j', k', rfl⟩ := (szb_mem_Q H.rel H.gen).1 (hBQ hβ)
      obtain ⟨l, hl5, hl⟩ := szb_exists_l (k := (k : ℤ)) (k' : ℤ) hk
      obtain ⟨I, J, hznf⟩ : ∃ I J : ℤ, (a ^ i' * c ^ j' * y ^ k') * (a ^ i * c ^ j * y ^ k) ^ l =
          a ^ I * c ^ J * y ^ (k' + k * l) :=
        ⟨_, _, by rw [szb_pow_formula H.rel, szb_mul H.rel]⟩
      have hz : a ^ I * c ^ J * y ^ (k' + k * l) ∈ B := by
        rw [← hznf]; exact mul_mem hβ (pow_mem hb l)
      have hcomm := szb_comm_of_isMulComm hB hz hb
      obtain ⟨h1, h2⟩ := (szb_b2_commute H I J i j (k' + k * l) k).1 hcomm
      have hK : (5 : ℤ) ∣ ((k' + k * l : ℕ) : ℤ) := by push_cast; exact hl
      have h1' : (5 : ℤ) ∣ (k : ℤ) * I := (dvd_sub_right (Dvd.dvd.mul_right hK i)).1 h1
      have h2' : (5 : ℤ) ∣ (k : ℤ) * J := (dvd_sub_right (Dvd.dvd.mul_right hK j)).1 h2
      obtain ⟨I₀, hI₀⟩ := szb_dvd5_mul hk h1'
      obtain ⟨J₀, hJ₀⟩ := szb_dvd5_mul hk h2'
      have hzZ : a ^ I * c ^ J * y ^ (k' + k * l) ∈ sz32Z a c := by
        refine (szb_b2_mem_Z H).2 ⟨I₀, J₀, ?_⟩
        have := (szb_b2_nf_eq_iff H (i := I) (j := J) (i' := 5 * I₀) (j' := 5 * J₀)
          (k := k' + k * l) (k' := 0)).2 ⟨by omega, by omega, by simpa using hK⟩
        simpa using this
      refine ⟨_, hzZ, ⟨l, hl5⟩, ?_⟩
      show _ = _ * ((a ^ i * c ^ j * y ^ k) ^ l)⁻¹
      rw [← hznf]; group
    let f : sz32Z a c × Fin 5 → X := fun p =>
      (p.1 : X) * ((a ^ i * c ^ j * y ^ k) ^ (p.2 : ℕ))⁻¹
    have hsub : (B : Set X) ⊆ Set.range f := by
      intro β hβ
      obtain ⟨z, hz, l, hl⟩ := hcover β hβ
      exact ⟨(⟨z, hz⟩, l), hl.symm⟩
    have h1 : Nat.card B ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hsub
    have h2 : Nat.card (Set.range f) ≤ Nat.card (sz32Z a c × Fin 5) :=
      Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    have h3 : Nat.card (sz32Z a c × Fin 5) = 5 ^ 2 * 5 := by
      rw [Nat.card_prod, szb_b2_card_Z H]; simp
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [szb_b2_card_Q0 H]; exact hcard)

theorem sz32_pgroup_facts {Q : Subgroup X} {a c y x : X} (hQ : Sz32QPres Q a c y x)
    (hc : orderOf c = 25) (hyc : y * c * y⁻¹ ≠ c) : Sz32QFacts Q a c y x := by
  obtain ⟨s, t, H⟩ := szb_b2_of_pres hQ hc hyc
  exact
  { ord_c := hc
    x_eq := szb_x_eq hc hQ.x_mem hQ.x_ord
    yc_ne := hyc
    card := szb_b2_card_Q H
    Q0_card := szb_b2_card_Q0 H
    Q0_comm := szb_b2_Q0_comm H
    Q0_unique := szb_b2_Q0_unique H
    center := szb_b2_center H
    Z_card := szb_b2_card_Z H
    Z_elem := szb_b2_Z_elem H
    comm_eq := szb_b2_comm_eq H
    pow5 := szb_b2_pow5_mem H
    pow5_surj := szb_b2_pow5_surj H
    exp := szb_b2_exp H
    Om_le := szb_b2_Om_le H
    Om_card := szb_b2_card_Om H
    Om_elem := szb_b2_Om_elem H
    Om_all := szb_b2_Om_all H
    cent_le := szb_b2_cent_le H
    shear := szb_b2_shear H }

theorem sz32_pgroup_struct {Q : Subgroup X} {a c y x g : X} (hQ : Sz32QPres Q a c y x)
    (hg : g ∈ Subgroup.normalizer (Q : Set X))
    (hswap : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (a ^ 5)) :
    Sz32QFacts Q a c y x :=
  sz32_pgroup_facts hQ (sz32_pgroup_swap hQ hg hswap).1 (sz32_pgroup_swap hQ hg hswap).2

end Abstract

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
