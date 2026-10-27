module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingBasic

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G]

theorem involution_mul_pow {s t : G} (hs : s * s = 1) (ht : t * t = 1) (j : ℕ) :
    s * (s * t) ^ j = ((s * t) ^ j)⁻¹ * s := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hsemi : SemiconjBy s (s * t) (s * t)⁻¹ := by
    change s * (s * t) = (s * t)⁻¹ * s
    rw [mul_inv_rev, htinv, hsinv, ← mul_assoc, hs, one_mul, mul_assoc, hs, mul_one]
  have hpow := hsemi.pow_right j
  rw [inv_pow] at hpow
  exact hpow.eq

theorem pow_inv_eq {s t : G} (hs : s * s = 1) (ht : t * t = 1) (j : ℕ) :
    ((s * t) ^ j)⁻¹ = s * (s * t) ^ j * s := by
  rw [involution_mul_pow hs ht j, mul_assoc, hs, mul_one]

theorem pow_two_mul_eq {s t : G} (hs : s * s = 1) (ht : t * t = 1) (j : ℕ) :
    (s * t) ^ (2 * j) * s = (s * t) ^ j * s * ((s * t) ^ j)⁻¹ := by
  rw [pow_inv_eq hs ht j, two_mul, pow_add]
  calc (s * t) ^ j * (s * t) ^ j * s = (s * t) ^ j * 1 * (s * t) ^ j * s := by rw [mul_one]
    _ = (s * t) ^ j * (s * s) * (s * t) ^ j * s := by rw [hs]
    _ = (s * t) ^ j * s * (s * (s * t) ^ j * s) := by simp only [mul_assoc]

theorem pow_two_add_one_mul_eq {s t : G} (hs : s * s = 1) (ht : t * t = 1) (j : ℕ) :
    (s * t) ^ (2 * j + 1) * s = (s * t) ^ j * (s * t * s) * ((s * t) ^ j)⁻¹ := by
  rw [pow_inv_eq hs ht j]
  have hcomm : (s * t) ^ j * (s * t) = (s * t) * (s * t) ^ j :=
    ((Commute.refl (s * t)).pow_left j).eq
  calc (s * t) ^ (2 * j + 1) * s = (s * t) ^ j * ((s * t) ^ j * (s * t)) * s := by
        rw [pow_succ, two_mul, pow_add, mul_assoc ((s * t) ^ j)]
    _ = (s * t) ^ j * ((s * t) * (s * t) ^ j) * s := by rw [hcomm]
    _ = (s * t) ^ j * (s * t) * (s * t) ^ j * s := by simp only [mul_assoc]
    _ = (s * t) ^ j * (s * t) * (s * s) * (s * t) ^ j * s := by rw [hs, mul_one]
    _ = (s * t) ^ j * (s * t * s) * (s * (s * t) ^ j * s) := by simp only [mul_assoc]

variable {z : G}

theorem rotation_mul_mem_class (hz : orderOf z = 2) {s t : G}
    (hs : s ∈ involutionPointClass z) (ht : t ∈ involutionPointClass z) (n : ℕ) :
    (s * t) ^ n * s ∈ involutionPointClass z := by
  have hss := class_mul_self hz hs
  have htt := class_mul_self hz ht
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [pow_two_mul_eq hss htt j]
    simpa only [inv_inv] using class_conj_mem hs ((s * t) ^ j)⁻¹
  · rw [pow_two_add_one_mul_eq hss htt j]
    have hsts : s * t * s ∈ involutionPointClass z := by
      simpa only [class_inv hz hs] using class_conj_mem ht s
    simpa only [inv_inv] using class_conj_mem hsts ((s * t) ^ j)⁻¹

theorem odd_product_conj (hz : orderOf z = 2) {s t : G}
    (hs : s ∈ involutionPointClass z) (ht : t ∈ involutionPointClass z)
    (hodd : Odd (orderOf (s * t))) :
    ∃ g ∈ Subgroup.zpowers (s * t), t = g⁻¹ * s * g := by
  have hss := class_mul_self hz hs
  have htt := class_mul_self hz ht
  obtain ⟨m, hm⟩ := hodd
  refine ⟨((s * t) ^ m)⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _), ?_⟩
  rw [inv_inv, ← pow_two_mul_eq hss htt m]
  have hone : (s * t) ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  have h : (s * t) ^ (2 * m) = (s * t)⁻¹ := by
    rw [pow_succ] at hone
    exact eq_inv_of_mul_eq_one_left hone
  rw [h, mul_inv_rev, inv_eq_of_mul_eq_one_left htt, inv_eq_of_mul_eq_one_left hss,
    mul_assoc, hss, mul_one]

theorem even_product_central [Finite G] (hz : orderOf z = 2) {s t : G}
    (hs : s ∈ involutionPointClass z) (ht : t ∈ involutionPointClass z)
    (heven : Even (orderOf (s * t))) :
    ∃ c : G, orderOf c = 2 ∧ c ∈ Subgroup.zpowers (s * t) ∧ Commute s c ∧ Commute t c ∧
      c * s ∈ involutionPointClass z ∧ c * t ∈ involutionPointClass z := by
  have hss := class_mul_self hz hs
  have htt := class_mul_self hz ht
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  set k := orderOf (s * t) / 2 with hk
  let c := (s * t) ^ k
  have hc : orderOf c = 2 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos (s * t))) heven.two_dvd
  have hcinv : c⁻¹ = c := inv_eq_self_of_orderOf_eq_two hc
  have hsc : Commute s c := by
    change s * c = c * s
    have h := involution_mul_pow hss htt k
    change s * c = c⁻¹ * s at h
    rw [h, hcinv]
  have hts : (t * s) = (s * t)⁻¹ := by rw [mul_inv_rev, hsinv, htinv]
  have hc' : (t * s) ^ k = c := by
    rw [hts, inv_pow]
    exact hcinv
  have htc : Commute t c := by
    change t * c = c * t
    have h := involution_mul_pow htt hss k
    rw [hc'] at h
    rw [h, hcinv]
  refine ⟨c, hc, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _, hsc, htc,
    rotation_mul_mem_class hz hs ht k, ?_⟩
  rw [← hc']
  exact rotation_mul_mem_class hz ht hs k

end CFSG.ComponentClassification.AschbacherStrongEmbedding
