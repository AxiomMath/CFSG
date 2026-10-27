module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Wreathed.BrauerWreathedOrder

universe u

variable {G : Type u} [Group G]

theorem exists_three_power_cycle [Finite G] (a b c Y : G) (h1 : Y⁻¹ * a * Y = b)
    (h2 : Y⁻¹ * b * Y = c) (h3 : Y⁻¹ * c * Y = a) :
    ∃ Z : G, (∃ k : ℕ, orderOf Z = 3 ^ k) ∧ Z⁻¹ * a * Z = b ∧ Z⁻¹ * b * Z = c ∧
      Z⁻¹ * c * Z = a := by
  have hfix : ∀ u, Y⁻¹ * (Y⁻¹ * (Y⁻¹ * u * Y) * Y) * Y = u → Commute (Y ^ 3) u := by
    intro u hu
    have h : (Y ^ 3)⁻¹ * u * Y ^ 3 = u := by
      have hY3 : Y ^ 3 = Y * Y * Y := by rw [pow_succ, pow_succ, pow_one]
      rw [hY3]
      calc (Y * Y * Y)⁻¹ * u * (Y * Y * Y) = Y⁻¹ * (Y⁻¹ * (Y⁻¹ * u * Y) * Y) * Y := by group
        _ = u := hu
    have h' : u * Y ^ 3 = Y ^ 3 * u := by
      calc u * Y ^ 3 = Y ^ 3 * ((Y ^ 3)⁻¹ * u * Y ^ 3) := by group
        _ = Y ^ 3 * u := by rw [h]
    exact h'.symm
  have ha : Commute (Y ^ 3) a := hfix a (by rw [h1, h2, h3])
  have hb : Commute (Y ^ 3) b := hfix b (by rw [h2, h3, h1])
  have hc : Commute (Y ^ 3) c := hfix c (by rw [h3, h1, h2])
  have hpow : ∀ q : ℕ, ∀ u v : G, Commute (Y ^ 3) u → Y⁻¹ * u * Y = v →
      (Y ^ (3 * q + 1))⁻¹ * u * Y ^ (3 * q + 1) = v := by
    intro q u v hu huv
    have hq : Commute ((Y ^ 3) ^ q) u := hu.pow_left q
    rw [pow_succ, pow_mul]
    calc ((Y ^ 3) ^ q * Y)⁻¹ * u * ((Y ^ 3) ^ q * Y) =
        Y⁻¹ * (((Y ^ 3) ^ q)⁻¹ * u * (Y ^ 3) ^ q) * Y := by group
      _ = Y⁻¹ * u * Y := by
        rw [show ((Y ^ 3) ^ q)⁻¹ * u * (Y ^ 3) ^ q = u by
          rw [mul_assoc, ← hq.eq, ← mul_assoc, inv_mul_cancel, one_mul]]
      _ = v := huv
  obtain ⟨e, k, hk3, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos Y).ne' 3
    (by norm_num)
  have hk1 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  obtain ⟨j, hj, hjord⟩ : ∃ j : ℕ, j % 3 = 1 ∧ (Y ^ j) ^ 3 ^ e = 1 := by
    rcases hk1 with h | h
    · refine ⟨k, h, ?_⟩
      rw [← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    · refine ⟨2 * k, by omega, ?_⟩
      rw [← pow_mul, show 2 * k * 3 ^ e = orderOf Y * 2 by rw [hk]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
  refine ⟨Y ^ j, ?_, ?_, ?_, ?_⟩
  · have hdvd : orderOf (Y ^ j) ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hjord
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact ⟨i, hi⟩
  all_goals
    rw [show j = 3 * (j / 3) + 1 by omega]
  · exact hpow _ a b ha h1
  · exact hpow _ b c hb h2
  · exact hpow _ c a hc h3

theorem order_formula_arith (g cJ cJ1 cD o oJ oJ1 oJ2 oD : ℕ) (hoJ : 0 < oJ) (hoD : 0 < oD)
    (h1 : g * oJ = cJ * o) (h2 : cJ1 * oD = oJ1 * cD) (h3 : oJ2 = oJ1)
    (hBW : o * oD ^ 2 = oJ1 * oJ2 * oJ) : g * cD ^ 2 = cJ * cJ1 ^ 2 := by
  subst h3
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hoJ (pow_pos hoD 2))
  calc g * cD ^ 2 * (oJ * oD ^ 2) = (g * oJ) * cD ^ 2 * oD ^ 2 := by ring
    _ = cJ * cD ^ 2 * (o * oD ^ 2) := by rw [h1]; ring
    _ = cJ * cD ^ 2 * (oJ2 * oJ2 * oJ) := by rw [hBW]
    _ = cJ * (oJ2 * cD) ^ 2 * oJ := by ring
    _ = cJ * (cJ1 * oD) ^ 2 * oJ := by rw [h2]
    _ = cJ * cJ1 ^ 2 * (oJ * oD ^ 2) := by ring

theorem centralizer_pair_eq (a b : G) :
    Subgroup.centralizer ({a, b} : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem centralizer_mem_mul_of_central_mod [Finite G] (O : Subgroup G) [O.Normal]
    (hO : Odd (Nat.card O)) {J J₁ : G} (hJ : J * J = 1)
    (hcen : ∀ g : G, g * J * g⁻¹ * J⁻¹ ∈ O) (hJJ₁ : J * J₁ = J₁ * J)
    {g : G} (hg : g ∈ Subgroup.centralizer ({J₁} : Set G)) :
    ∃ o ∈ O ⊓ Subgroup.centralizer ({J₁} : Set G),
      ∃ c ∈ Subgroup.centralizer ({J} : Set G) ⊓ Subgroup.centralizer ({J₁} : Set G),
        g = o * c := by
  have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ
  have hgJ₁ : g * J₁ = J₁ * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  set w := g * J * g⁻¹ with hw
  set m := J * w with hm
  have hmO : m ∈ O := by
    have h := hcen g
    rw [hJinv] at h
    have h2 := O.inv_mem h
    have h3 : (g * J * g⁻¹ * J)⁻¹ = J * w := by
      calc (g * J * g⁻¹ * J)⁻¹ = J⁻¹ * (g * J⁻¹ * g⁻¹) := by group
        _ = J * w := by rw [hJinv]
    rw [h3] at h2
    exact h2
  have hww : w * w = 1 := by
    rw [hw]
    calc g * J * g⁻¹ * (g * J * g⁻¹) = g * (J * J) * g⁻¹ := by group
      _ = 1 := by rw [hJ]; group
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hwJ₁ : w * J₁ = J₁ * w := by
    rw [hw]
    calc g * J * g⁻¹ * J₁ = g * J * (g⁻¹ * J₁) := by group
      _ = g * J * (J₁ * g⁻¹) := by
        rw [show g⁻¹ * J₁ = J₁ * g⁻¹ by
          calc g⁻¹ * J₁ = g⁻¹ * (J₁ * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * J₁) * g⁻¹ := by rw [hgJ₁]
            _ = J₁ * g⁻¹ := by group]
      _ = g * (J * J₁) * g⁻¹ := by group
      _ = g * (J₁ * J) * g⁻¹ := by rw [hJJ₁]
      _ = (g * J₁) * J * g⁻¹ := by group
      _ = J₁ * g * J * g⁻¹ := by rw [hgJ₁]
      _ = J₁ * (g * J * g⁻¹) := by group
  have hmJ₁ : m * J₁ = J₁ * m := by
    rw [hm]
    calc J * w * J₁ = J * (w * J₁) := by group
      _ = J * (J₁ * w) := by rw [hwJ₁]
      _ = (J * J₁) * w := by group
      _ = (J₁ * J) * w := by rw [hJJ₁]
      _ = J₁ * (J * w) := by group
  have hJm : J * m * J⁻¹ = m⁻¹ := by
    rw [hm, hJinv, mul_inv_rev, hwinv, hJinv]
    calc J * (J * w) * J = (J * J) * w * J := by group
      _ = w * J := by rw [hJ, one_mul]
  obtain ⟨k, hk⟩ : Odd (orderOf m) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hmO)
  set r := m ^ (k + 1) with hr
  have hrO : r ∈ O := O.pow_mem hmO _
  have hrr : r * r = m := by
    rw [hr, ← pow_add, show k + 1 + (k + 1) = orderOf m + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hrJ₁ : r * J₁ = J₁ * r := by
    rw [hr]
    exact ((Commute.pow_left hmJ₁ (k + 1))).eq
  have hJr : J * r * J⁻¹ = r⁻¹ := by
    rw [hr, ← conj_pow, hJm, inv_pow]
  have hrw : r⁻¹ * J * r = w := by
    have hJr' : J * r = r⁻¹ * J := by
      calc J * r = (J * r * J⁻¹) * J := by group
        _ = r⁻¹ * J := by rw [hJr]
    calc r⁻¹ * J * r = r⁻¹ * (J * r) := by group
      _ = r⁻¹ * (r⁻¹ * J) := by rw [hJr']
      _ = (r * r)⁻¹ * J := by group
      _ = m⁻¹ * J := by rw [hrr]
      _ = w := by
        rw [hm, mul_inv_rev, hJinv, hwinv, mul_assoc, hJ, mul_one]
  refine ⟨r⁻¹, ⟨O.inv_mem hrO, ?_⟩, r * g, ⟨?_, ?_⟩, by group⟩
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    calc r⁻¹ * J₁ = r⁻¹ * (J₁ * r) * r⁻¹ := by group
      _ = r⁻¹ * (r * J₁) * r⁻¹ := by rw [hrJ₁]
      _ = J₁ * r⁻¹ := by group
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h1 : r * g * J * (r * g)⁻¹ = J := by
      calc r * g * J * (r * g)⁻¹ = r * (g * J * g⁻¹) * r⁻¹ := by group
        _ = r * w * r⁻¹ := by rw [← hw]
        _ = r * (r⁻¹ * J * r) * r⁻¹ := by rw [hrw]
        _ = J := by group
    calc r * g * J = (r * g * J * (r * g)⁻¹) * (r * g) := by group
      _ = J * (r * g) := by rw [h1]
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    calc r * g * J₁ = r * (g * J₁) := by group
      _ = r * (J₁ * g) := by rw [hgJ₁]
      _ = (r * J₁) * g := by group
      _ = (J₁ * r) * g := by rw [hrJ₁]
      _ = J₁ * (r * g) := by group

end CFSG.Wreathed.BrauerWreathedOrder
