module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingProducts

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G] {H : Subgroup G} {z : G}

theorem zpow_semiconj_or {x y : G} (hy : SemiconjBy y x x⁻¹) (n : ℤ) :
    SemiconjBy (y ^ n) x x ∨ SemiconjBy (y ^ n) x x⁻¹ := by
  have hy' : SemiconjBy y x⁻¹ x := by simpa only [inv_inv] using hy.inv_right
  have hsq : Commute (y ^ (2 : ℤ)) x := by
    rw [zpow_two]
    exact hy'.mul_left hy
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul]
    exact (hsq.zpow_left m : Commute _ x)
  · right
    rw [zpow_add_one, zpow_mul]
    exact SemiconjBy.mul_left ((hsq.zpow_left m).inv_right) hy

theorem commute_conj_of_semiconj {g z x x' : G} (hsemi : SemiconjBy g x x')
    (hzx : Commute z x') : Commute (g⁻¹ * z * g) x := by
  have hx : x = g⁻¹ * x' * g := by rw [mul_assoc, ← hsemi.eq, inv_mul_cancel_left]
  rw [hx]
  change g⁻¹ * z * g * (g⁻¹ * x' * g) = g⁻¹ * x' * g * (g⁻¹ * z * g)
  calc g⁻¹ * z * g * (g⁻¹ * x' * g) = g⁻¹ * (z * x') * g := by group
    _ = g⁻¹ * (x' * z) * g := by rw [hzx.eq]
    _ = g⁻¹ * x' * g * (g⁻¹ * z * g) := by group

theorem factors_mem_of_product_centralizing [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h1 : ProductUniqueContainment H z)
    {t s : G} (ht : t ∈ involutionPointClass z) (hs : s ∈ involutionPointClass z)
    (hne : t * s ≠ 1) (hcent : Commute (t * s) z) : t ∈ H ∧ s ∈ H := by
  have htt := class_mul_self hz ht
  have hss := class_mul_self hz hs
  have hzcls : z ∈ involutionPointClass z := distinguished_mem_pointClass z
  have hxH : t * s ∈ H := centralizer_le_of_unique huniq
    (Subgroup.mem_centralizer_singleton_iff.mpr hcent.eq)
  suffices htH : t ∈ H by
    refine ⟨htH, ?_⟩
    have hmem := H.mul_mem htH hxH
    rwa [← mul_assoc, htt, one_mul] at hmem
  by_contra htH
  have htω : t • (QuotientGroup.mk 1 : G ⧸ H) ≠ QuotientGroup.mk 1 :=
    fun h => htH (class_mem_iff_fixes_base.mpr h)
  have hzω : z • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 :=
    (smul_eq_iff_eq_base huniq _).mpr rfl
  by_cases heven : Even (orderOf (t * s))
  · obtain ⟨c, hc, hcpow, htc, -, hct, -⟩ := even_product_central hz ht hs heven
    have hcz : Commute c z := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcpow
      exact hcent.zpow_left n
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hc
      exact absurd hc (by decide)
    have hctne : c * t ≠ t := fun h => hc1 (mul_eq_right.mp h)
    have hctc : t * (c * t) = c := by rw [← mul_assoc, htc.eq, mul_assoc, htt, mul_one]
    have key : ∀ ω : G ⧸ H, c • ω = ω ↔ t • ω = ω := by
      intro ω
      rw [← hctc]
      exact product_smul_eq_iff huniq h1 ht hct (htc.mul_right (Commute.refl t)) hctne ω
    obtain ⟨ωt, hωt⟩ := class_fixes_unique huniq ht
    have hcωt : c • ωt = ωt := (key ωt).mpr ((hωt ωt).mpr rfl)
    have hczω : c • (z • ωt) = z • ωt := by
      rw [← mul_smul, hcz.eq, mul_smul, hcωt]
    have hzωt : z • ωt = ωt := (hωt _).mp ((key _).mp hczω)
    have hωbase : ωt = QuotientGroup.mk 1 := (smul_eq_iff_eq_base huniq ωt).mp hzωt
    exact htω (by rw [← hωbase]; exact (hωt ωt).mpr rfl)
  · have hodd : Odd (orderOf (t * s)) := Nat.not_even_iff_odd.mp heven
    obtain ⟨g, hg, hgt⟩ := odd_product_conj hz hzcls ht
      (odd_product_of_fixes_ne hz huniq h1 hzcls ht hzω htω)
    have htinv : SemiconjBy t (t * s) (t * s)⁻¹ := by
      change t * (t * s) = (t * s)⁻¹ * t
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_left hss, inv_eq_of_mul_eq_one_left htt,
        ← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
    have hzx : Commute z (t * s)⁻¹ := hcent.symm.inv_right
    have hztinv : SemiconjBy (z * t) (t * s) (t * s)⁻¹ := SemiconjBy.mul_left hzx htinv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have htx : Commute t (t * s) := by
      nth_rewrite 1 [hgt]
      rcases zpow_semiconj_or hztinv n with hsemi | hsemi
      · exact commute_conj_of_semiconj hsemi hcent.symm
      · exact commute_conj_of_semiconj hsemi hzx
    have hxx : t * s = (t * s)⁻¹ := by
      have h1' := htinv.eq
      rw [htx.eq] at h1'
      exact mul_right_cancel h1'
    have hsq : (t * s) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hxx]
      exact mul_inv_cancel _
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact hne (orderOf_eq_one_iff.mp h)
    · rw [h] at hodd
      exact absurd hodd (by decide)

end CFSG.ComponentClassification.AschbacherStrongEmbedding
