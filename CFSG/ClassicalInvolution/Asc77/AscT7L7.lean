module

public import CFSG.ClassicalInvolution.Asc77.AscT7L2

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement

namespace T7L

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem isSylow2In_sup_of_normalizes {N R : Subgroup G} (hNodd : Odd (Nat.card N))
    (hR2 : IsPGroup 2 R) (hRN : R ≤ Subgroup.normalizer (N : Set G)) : IsSylow2In R (N ⊔ R) := by
  refine ⟨le_sup_right, hR2, fun V hVT hV2 hRV => ?_⟩
  refine le_antisymm (fun x hx => ?_) hRV
  obtain ⟨n, hn, r, hr, rfl⟩ := mem_sup_normalForm hRN (hVT hx)
  have hnV : n ∈ V := by
    have : n = (n * r) * r⁻¹ := by group
    rw [this]
    exact V.mul_mem hx (V.inv_mem (hRV hr))
  have hn1 : n = 1 :=
    eq_one_of_isPGroup_of_mem_odd hNodd hn (hV2.to_le (Subgroup.zpowers_le.mpr hnV))
  rw [hn1, one_mul]
  exact hr

omit [Finite G] in
theorem zpow_involution {s : G} (hs2 : s * s = 1) (k : ℤ) : s ^ k = 1 ∨ s ^ k = s := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, hs2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hs2, one_zpow, one_mul]

theorem exists_conj_involution {N : Subgroup G} {s s' : G} (hNodd : Odd (Nat.card N))
    (hs2 : s * s = 1) (hs'2 : s' * s' = 1) (hs'1 : s' ≠ 1)
    (hsN : s ∈ Subgroup.normalizer (N : Set G)) (hss' : s⁻¹ * s' ∈ N) :
    ∃ n ∈ N, s' = n * s * n⁻¹ := by
  have hs : s' = s * (s⁻¹ * s') := by group
  have hs'N : s' ∈ Subgroup.normalizer (N : Set G) := by
    rw [hs]
    exact Subgroup.mul_mem _ hsN (Subgroup.le_normalizer hss')
  have hP2 : IsPGroup 2 (Subgroup.zpowers s) := isPGroup_zpowers_of_sq_eq_one hs2
  have hP'2 : IsPGroup 2 (Subgroup.zpowers s') := isPGroup_zpowers_of_sq_eq_one hs'2
  have hPN : Subgroup.zpowers s ≤ Subgroup.normalizer (N : Set G) := Subgroup.zpowers_le.mpr hsN
  have hP'N : Subgroup.zpowers s' ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr hs'N
  have hM : N ⊔ Subgroup.zpowers s' = N ⊔ Subgroup.zpowers s := by
    apply le_antisymm
    · refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
      rw [hs]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
        (Subgroup.mem_sup_left hss')
    · refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
      have : s = s' * (s⁻¹ * s')⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers s'))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hss'))
  have hS : IsSylow2In (Subgroup.zpowers s) (N ⊔ Subgroup.zpowers s) :=
    isSylow2In_sup_of_normalizes hNodd hP2 hPN
  have hS' : IsSylow2In (Subgroup.zpowers s') (N ⊔ Subgroup.zpowers s) := by
    rw [← hM]
    exact isSylow2In_sup_of_normalizes hNodd hP'2 hP'N
  obtain ⟨c, hc, hcP⟩ := exists_conj_sylow hS hS'
  obtain ⟨n, hn, r, hr, rfl⟩ := mem_sup_normalForm hPN hc
  have hcn : conjSub (n * r) (Subgroup.zpowers s) = conjSub n (Subgroup.zpowers s) := by
    rw [conjSub_mul, conjSub_eq_self_of_mem hr]
  rw [hcn] at hcP
  have hs'P : s' ∈ conjSub n (Subgroup.zpowers s) := by
    rw [hcP]
    exact Subgroup.mem_zpowers s'
  rw [mem_conjSub_iff] at hs'P
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs'P
  have hne1 : n⁻¹ * s' * n ≠ 1 := by
    intro h
    apply hs'1
    have := congrArg (fun x => n * x * n⁻¹) h
    simpa [mul_assoc] using this
  have hnsn : n⁻¹ * s' * n = s := by
    rcases zpow_involution hs2 k with h | h
    · exact absurd (hk.symm.trans h) hne1
    · exact hk.symm.trans h
  refine ⟨n, hn, ?_⟩
  calc s' = n * (n⁻¹ * s' * n) * n⁻¹ := by group
    _ = n * s * n⁻¹ := by rw [hnsn]

theorem eq_mul_of_conj_mod {H Y N : Subgroup G} (hYH : Y ≤ H) (hNY : N ≤ Y)
    (hNodd : Odd (Nat.card N)) (hYN : ∀ y ∈ Y, y ∈ Subgroup.normalizer (N : Set G)) {t : G}
    (htY : t ∈ Y) (ht2 : t * t = 1) (ht1 : t ≠ 1) {h : G} (hh : h ∈ H) {y : G} (hy : y ∈ Y)
    (hcongr : t⁻¹ * (y⁻¹ * (h * t * h⁻¹) * y) ∈ N) :
    ∃ y' ∈ Y, ∃ c ∈ H ⊓ Subgroup.centralizer ({t} : Set G), h = y' * c := by
  set s' := y⁻¹ * (h * t * h⁻¹) * y with hs'
  have hs'2 : s' * s' = 1 := by
    calc s' * s' = y⁻¹ * h * (t * t) * h⁻¹ * y := by simp only [hs']; group
      _ = 1 := by rw [ht2]; group
  have hs'1 : s' ≠ 1 := by
    intro h1
    apply ht1
    have h2 : t = (h⁻¹ * y) * s' * (h⁻¹ * y)⁻¹ := by simp only [hs']; group
    rw [h1] at h2
    simpa using h2
  obtain ⟨n, hn, hns⟩ := exists_conj_involution hNodd ht2 hs'2 hs'1 (hYN t htY) hcongr
  refine ⟨y * n, Y.mul_mem hy (hNY hn), n⁻¹ * y⁻¹ * h, ⟨?_, ?_⟩, ?_⟩
  · exact H.mul_mem (H.mul_mem (H.inv_mem (hYH (hNY hn))) (H.inv_mem (hYH hy))) hh
  · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 : n⁻¹ * s' * n = t := by
      rw [hns]
      group
    calc n⁻¹ * y⁻¹ * h * t = (n⁻¹ * s' * n) * (n⁻¹ * y⁻¹ * h) := by simp only [hs']; group
      _ = t * (n⁻¹ * y⁻¹ * h) := by rw [h1]
  · group

end Coprime

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_centralizer_of_comm_mod {N : Subgroup G} {s y : G} (hNodd : Odd (Nat.card N))
    (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsN : s ∈ Subgroup.normalizer (N : Set G))
    (h : s⁻¹ * (y * s * y⁻¹) ∈ N) :
    ∃ n ∈ N, ∃ c ∈ Subgroup.centralizer ({s} : Set G), y = n * c := by
  have hs'2 : (y * s * y⁻¹) * (y * s * y⁻¹) = 1 := by
    calc (y * s * y⁻¹) * (y * s * y⁻¹) = y * (s * s) * y⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hs'1 : y * s * y⁻¹ ≠ 1 := by
    intro h1
    apply hs1
    have := congrArg (fun x => y⁻¹ * x * y) h1
    simpa [mul_assoc] using this
  obtain ⟨n, hn, hns⟩ := exists_conj_involution hNodd hs2 hs'2 hs'1 hsN h
  refine ⟨n, hn, n⁻¹ * y, ?_, by group⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc n⁻¹ * y * s = (n⁻¹ * (y * s * y⁻¹) * n) * (n⁻¹ * y) := by group
    _ = s * (n⁻¹ * y) := by rw [hns]; group

end Lift

end T7L

end CFSG.ClassicalInvolution.Asc77
