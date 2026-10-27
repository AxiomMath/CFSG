module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolPsp4

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.Assembly.LowTwoRank FooteLit CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_pow_eq_inv_of_conj_eq_inv {t r : G} (h : t * r * t⁻¹ = r⁻¹) (k : ℕ) :
    t * r ^ k * t⁻¹ = (r ^ k)⁻¹ := by
  rw [← conj_pow, h, inv_pow]

omit [Finite G] in
theorem conj_mul_eq_inv {z a : G} (hz : z * z = 1) (ha : a * a = 1) :
    z * (z * a) * z⁻¹ = (z * a)⁻¹ ∧ a * (z * a) * a⁻¹ = (z * a)⁻¹ := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [mul_inv_rev, hainv, hzinv]
  constructor
  · rw [← mul_assoc, hz, one_mul]
  · simp only [mul_assoc, ha, mul_one]

omit [Finite G] in
theorem exists_conj_of_odd_orderOf {z a : G} (hz : z * z = 1) (ha : a * a = 1)
    (hodd : Odd (orderOf (z * a))) : ∃ k : ℕ, ((z * a) ^ k)⁻¹ * z * (z * a) ^ k = a := by
  obtain ⟨j, hj⟩ := hodd
  refine ⟨j + 1, ?_⟩
  rw [← conj_pow_eq_inv_of_conj_eq_inv (conj_mul_eq_inv hz ha).1]
  have h2 : (z * a) ^ (j + 1) * (z * a) ^ (j + 1) = z * a := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf (z * a) + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  calc z * (z * a) ^ (j + 1) * z⁻¹ * z * (z * a) ^ (j + 1)
      = z * ((z * a) ^ (j + 1) * (z * a) ^ (j + 1)) := by
        simp only [mul_assoc, inv_mul_cancel_left]
    _ = a := by rw [h2, ← mul_assoc, hz, one_mul]

theorem dihedral_center {z a : G} (hz : z * z = 1) (ha : a * a = 1)
    (heven : Even (orderOf (z * a))) :
    orderOf ((z * a) ^ (orderOf (z * a) / 2)) = 2 ∧
      (z * a) ^ (orderOf (z * a) / 2) * z = z * (z * a) ^ (orderOf (z * a) / 2) ∧
      (z * a) ^ (orderOf (z * a) / 2) * a = a * (z * a) ^ (orderOf (z * a) / 2) := by
  have hco : orderOf ((z * a) ^ (orderOf (z * a) / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos (z * a)).ne' (even_iff_two_dvd.mp heven)
  have hcc : ((z * a) ^ (orderOf (z * a) / 2))⁻¹ = (z * a) ^ (orderOf (z * a) / 2) := by
    apply inv_eq_of_mul_eq_one_right
    have h := pow_orderOf_eq_one ((z * a) ^ (orderOf (z * a) / 2))
    rwa [hco, pow_two] at h
  obtain ⟨h1, h2⟩ := conj_mul_eq_inv hz ha
  have hzc := conj_pow_eq_inv_of_conj_eq_inv h1 (orderOf (z * a) / 2)
  have hac := conj_pow_eq_inv_of_conj_eq_inv h2 (orderOf (z * a) / 2)
  rw [hcc] at hzc hac
  exact ⟨hco, (mul_inv_eq_iff_eq_mul.mp hzc).symm, (mul_inv_eq_iff_eq_mul.mp hac).symm⟩

omit [Finite G] in
theorem le_centralizer_pow {z a : G} {A : Subgroup G} (hz : A ≤ centralizer ({z} : Set G))
    (ha : A ≤ centralizer ({a} : Set G)) (k : ℕ) :
    A ≤ centralizer ({(z * a) ^ k} : Set G) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  have h1 : Commute x z := mem_centralizer_singleton_iff.mp (hz hx)
  have h2 : Commute x a := mem_centralizer_singleton_iff.mp (ha hx)
  exact ((h1.mul_right h2).pow_right k).eq

omit [Finite G] in
theorem mem_normalizer_of_le_centralizer {g : G} {A : Subgroup G}
    (h : A ≤ centralizer ({g} : Set G)) : g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have e : x * g = g * x := mem_centralizer_singleton_iff.mp (h hx)
    rw [← e, mul_inv_cancel_right]
    exact hx
  · intro hx
    have e : g * x * g⁻¹ * g = g * (g * x * g⁻¹) := mem_centralizer_singleton_iff.mp (h hx)
    have hx' : x = g * x * g⁻¹ := by
      calc x = g⁻¹ * (g * x * g⁻¹ * g) := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [e]
        _ = g * x * g⁻¹ := by group
    rw [hx']
    exact hx

end CFSG.ComponentClassification.Foote5.SolMax

