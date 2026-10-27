module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

variable {G : Type} [Group G] {t z : G}

theorem mem_V_iff (ht : t ^ 2 = 1) (hz : z ^ 2 = 1) (hc : t * z = z * t) {x : G} :
    x ∈ zpowers t ⊔ zpowers z ↔ x = 1 ∨ x = t ∨ x = z ∨ x = t * z := by
  have ht2 : t * t = 1 := by rw [← pow_two, ht]
  have hz2 : z * z = 1 := by rw [← pow_two, hz]
  have hzt : z * t = t * z := hc.symm
  have httz : t * (t * z) = z := by rw [← mul_assoc, ht2, one_mul]
  have htzt : (t * z) * t = z := by rw [mul_assoc, hzt, ← mul_assoc, ht2, one_mul]
  have hztz : z * (t * z) = t := by rw [← mul_assoc, hzt, mul_assoc, hz2, mul_one]
  have htzz : (t * z) * z = t := by rw [mul_assoc, hz2, mul_one]
  have htz2 : (t * z) * (t * z) = 1 := by rw [← mul_assoc, htzt, hz2]
  let W : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = t ∨ x = z ∨ x = t * z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        rcases ha with h | h | h | h <;> rcases hb with k | k | k | k
        all_goals rw [h, k]
        all_goals simp [ht2, hz2, hzt, httz, htzt, hztz, htzz, htz2]
      inv_mem' := by
        intro a ha
        rcases ha with h | h | h | h
        · rw [h]
          exact Or.inl (inv_one)
        · rw [h]
          exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ht2))
        · rw [h]
          exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hz2)))
        · rw [h]
          exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right htz2))) }
  have htW : t ∈ W := Or.inr (Or.inl rfl)
  have hzW : z ∈ W := Or.inr (Or.inr (Or.inl rfl))
  have hVW : zpowers t ⊔ zpowers z ≤ W :=
    sup_le (zpowers_le.mpr htW) (zpowers_le.mpr hzW)
  constructor
  · intro hx
    exact hVW hx
  · rintro (h | h | h | h)
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_sup_left (mem_zpowers t)
    · rw [h]
      exact mem_sup_right (mem_zpowers z)
    · rw [h]
      exact mul_mem_sup (mem_zpowers t) (mem_zpowers z)

private lemma conj_eq_self_iff_comm {g y : G} : g * y * g⁻¹ = y ↔ g * y = y * g := by
  constructor
  · intro h
    calc g * y = (g * y * g⁻¹) * g := by group
      _ = y * g := by rw [h]
  · intro h
    rw [h]
    group

private lemma conj_mem_V (ht : t ^ 2 = 1) (hz : z ^ 2 = 1) (hc : t * z = z * t) {g x : G}
    (hgz : g * z * g⁻¹ = z) (hgt : g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z)
    (hx : x ∈ zpowers t ⊔ zpowers z) : g * x * g⁻¹ ∈ zpowers t ⊔ zpowers z := by
  rw [mem_V_iff ht hz hc] at hx
  rcases hx with hx | hx | hx | hx
  · rw [hx, mul_one, mul_inv_cancel]
    exact one_mem _
  · rw [hx]
    rcases hgt with hgt | hgt
    · rw [hgt]
      exact mem_sup_left (mem_zpowers t)
    · rw [hgt]
      exact mul_mem_sup (mem_zpowers t) (mem_zpowers z)
  · rw [hx, hgz]
    exact mem_sup_right (mem_zpowers z)
  · rw [hx]
    have hconj : g * (t * z) * g⁻¹ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group
    rw [hconj]
    rcases hgt with hgt | hgt
    · rw [hgt, hgz]
      exact mul_mem_sup (mem_zpowers t) (mem_zpowers z)
    · rw [hgt, hgz, mul_assoc, ← pow_two, hz, mul_one]
      exact mem_sup_left (mem_zpowers t)

theorem mem_normalizer_V_of_conj (ht : t ^ 2 = 1) (hz : z ^ 2 = 1) (hc : t * z = z * t) {g : G}
    (hgz : g * z * g⁻¹ = z) (hgt : g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z) :
    g ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_V ht hz hc hgz hgt hx
  · intro hx
    have hcomm : g * z = z * g := conj_eq_self_iff_comm.mp hgz
    have hgz' : g⁻¹ * z * (g⁻¹)⁻¹ = z := by
      calc g⁻¹ * z * (g⁻¹)⁻¹ = g⁻¹ * (z * g) := by group
        _ = g⁻¹ * (g * z) := by rw [hcomm]
        _ = z := by rw [inv_mul_cancel_left]
    have hgt' : g⁻¹ * t * (g⁻¹)⁻¹ = t ∨ g⁻¹ * t * (g⁻¹)⁻¹ = t * z := by
      rcases hgt with h | h
      · left
        have hcommt : g * t = t * g := conj_eq_self_iff_comm.mp h
        calc g⁻¹ * t * (g⁻¹)⁻¹ = g⁻¹ * (t * g) := by group
          _ = g⁻¹ * (g * t) := by rw [hcommt]
          _ = t := by rw [inv_mul_cancel_left]
      · right
        have h1 : g⁻¹ * (t * z) * (g⁻¹)⁻¹ = t := by
          rw [← h]
          group
        have h2 : g⁻¹ * (t * z) * (g⁻¹)⁻¹
            = (g⁻¹ * t * (g⁻¹)⁻¹) * (g⁻¹ * z * (g⁻¹)⁻¹) := by group
        have haz : (g⁻¹ * t * (g⁻¹)⁻¹) * z = t := by
          rw [h2, hgz'] at h1
          exact h1
        calc g⁻¹ * t * (g⁻¹)⁻¹ = (g⁻¹ * t * (g⁻¹)⁻¹) * (z * z) := by
              rw [← pow_two, hz, mul_one]
          _ = ((g⁻¹ * t * (g⁻¹)⁻¹) * z) * z := by rw [← mul_assoc]
          _ = t * z := by rw [haz]
    have hmem := conj_mem_V ht hz hc (g := g⁻¹) hgz' hgt' hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at hmem

theorem normalizer_V_le_centralizer_z (ht : t ^ 2 = 1) (hz : z ^ 2 = 1) (hc : t * z = z * t)
    (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) :
    normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzV : n * z * n⁻¹ ∈ zpowers t ⊔ zpowers z :=
    (Subgroup.mem_set_normalizer_iff.mp hn z).mp (mem_sup_right (mem_zpowers z))
  rw [mem_V_iff ht hz hc] at hzV
  rcases hzV with h | h | h | h
  · have hz1 : z = 1 := by
      have hnz : n * z = n := by
        calc n * z = (n * z * n⁻¹) * n := by group
          _ = 1 * n := by rw [h]
          _ = n := by rw [one_mul]
      exact (mul_left_cancel_iff (a := n)).mp (by rw [mul_one]; exact hnz)
    rw [hz1]
    simp
  · exact absurd (IsConj.symm (isConj_iff.mpr ⟨n, h⟩)) hzt
  · exact conj_eq_self_iff_comm.mp h
  · exact absurd (htz.trans (isConj_iff.mpr ⟨n, h⟩).symm) hzt

theorem conj_t_of_mem_normalizer_V (ht : t ^ 2 = 1) (hz : z ^ 2 = 1) (hc : t * z = z * t)
    (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) {n : G}
    (hn : n ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G)) :
    n * t * n⁻¹ = t ∨ n * t * n⁻¹ = t * z := by
  have htV : n * t * n⁻¹ ∈ zpowers t ⊔ zpowers z :=
    (Subgroup.mem_set_normalizer_iff.mp hn t).mp (mem_sup_left (mem_zpowers t))
  rw [mem_V_iff ht hz hc] at htV
  rcases htV with h | h | h | h
  · left
    have ht1 : t = 1 := by
      have hnt : n * t = n := by
        calc n * t = (n * t * n⁻¹) * n := by group
          _ = 1 * n := by rw [h]
          _ = n := by rw [one_mul]
      exact (mul_left_cancel_iff (a := n)).mp (by rw [mul_one]; exact hnt)
    rw [ht1]
    simp
  · exact Or.inl h
  · exact absurd (isConj_iff.mpr ⟨n, h⟩) hzt
  · exact Or.inr h

theorem normalizer_V_inf_centralizer_t (ht : t ^ 2 = 1) (hz : z ^ 2 = 1) (hc : t * z = z * t)
    (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) :
    normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) =
      centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
  refine le_antisymm ?_ ?_
  · intro n hn
    exact ⟨hn.2, normalizer_V_le_centralizer_z ht hz hc hzt htz hn.1⟩
  · intro n hn
    refine ⟨?_, hn.1⟩
    refine mem_normalizer_V_of_conj ht hz hc ?_ (Or.inl ?_)
    · exact conj_eq_self_iff_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp hn.2)
    · exact conj_eq_self_iff_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp hn.1)

theorem conj_mem_centralizer_of_mem_normalizer_V (ht : t ^ 2 = 1) (hz : z ^ 2 = 1)
    (hc : t * z = z * t) (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) {n c : G}
    (hn : n ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G))
    (hc' : c ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) :
    n * c * n⁻¹ ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
  obtain ⟨hct, hcz⟩ := hc'
  have hcz' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hct' : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hct
  have hz' : n⁻¹ * z * n = z := by
    have := conj_eq_self_iff_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp
      (normalizer_V_le_centralizer_z ht hz hc hzt htz (inv_mem hn)))
    simpa [inv_inv] using this
  have ht' : n⁻¹ * t * n = t ∨ n⁻¹ * t * n = t * z := by
    have := conj_t_of_mem_normalizer_V ht hz hc hzt htz (inv_mem hn)
    simpa [inv_inv] using this
  have hc_nzn : c * (n⁻¹ * z * n) * c⁻¹ = n⁻¹ * z * n := by
    rw [hz']
    exact conj_eq_self_iff_comm.mpr hcz'
  have hctz : c * (t * z) = (t * z) * c := by
    rw [← mul_assoc, hct', mul_assoc, hcz', ← mul_assoc]
  have hc_ntn : c * (n⁻¹ * t * n) * c⁻¹ = n⁻¹ * t * n := by
    rcases ht' with h | h
    · rw [h]
      exact conj_eq_self_iff_comm.mpr hct'
    · rw [h]
      exact conj_eq_self_iff_comm.mpr hctz
  have hz_n : n * z * n⁻¹ = z :=
    conj_eq_self_iff_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp
      (normalizer_V_le_centralizer_z ht hz hc hzt htz hn))
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (conj_eq_self_iff_comm.mp (by
        calc (n * c * n⁻¹) * t * (n * c * n⁻¹)⁻¹
            = n * (c * (n⁻¹ * t * n) * c⁻¹) * n⁻¹ := by group
          _ = n * (n⁻¹ * t * n) * n⁻¹ := by rw [hc_ntn]
          _ = t := by group))
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (conj_eq_self_iff_comm.mp (by
        calc (n * c * n⁻¹) * z * (n * c * n⁻¹)⁻¹
            = n * (c * (n⁻¹ * z * n) * c⁻¹) * n⁻¹ := by group
          _ = n * (n⁻¹ * z * n) * n⁻¹ := by rw [hc_nzn]
          _ = z := by rw [hz']; exact hz_n))

end CFSG.EvenSporadicStandard.HNRecog.Harada
