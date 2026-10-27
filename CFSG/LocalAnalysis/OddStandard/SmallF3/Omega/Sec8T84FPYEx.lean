module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPList

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open Certificates.Asc82NormA6 (Facts)
open Certificates.T84P (mulE oneE M0l P0l Jl commE)

private lemma t84_conj_cube {M : Type*} [Group M] (g x : M) (hg : g ^ 3 = 1) :
    g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = x := by
  have h : g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = g ^ 3 * x * (g ^ 3)⁻¹ := by
    simp [pow_succ, mul_assoc]
  rw [h, hg]
  simp

theorem sec8t84FPy_exists (F : Facts) (G : Certificates.T84P.Facts) :
    ∃ y : Sec8T84FPM0 F, orderOf y = 3 ∧
      y ∈ normalizer ((sec8t84FPJ0 F G : Subgroup (Sec8T84FPM0 F)) : Set (Sec8T84FPM0 F)) ∧
      (∀ u ∈ sec8t84FPJ0 F G, y * u = u * y → u = 1) ∧
      ∃ s ∈ sec8t84FPP0 F G, s ∉ sec8t84FPJ0 F G ∧ orderOf s = 2 ∧ s * y * s⁻¹ = y⁻¹ ∧
        sec8t84FPP0 F G = zpowers s ⊔ sec8t84FPJ0 F G := by
  obtain ⟨y, hyM, hy_ne, hy_cube, hyJ, hyfix, s, hsP, hsJ, hs_sq, hs_sy, hsplit⟩ := G.y
  obtain ⟨y₀, hy⟩ := sec8t84FPRaw_surj F hyM
  obtain ⟨s₀, hs⟩ := sec8t84FPRaw_surj F (G.p0.2.2.2.1 s hsP)
  have hy0_ne : y₀ ≠ 1 := fun h => hy_ne (by rw [← hy, h, sec8t84FPRaw_one])
  have hcube0 : y₀ * (y₀ * y₀) = 1 := by
    apply sec8t84FPRaw_injective F
    simp only [sec8t84FPRaw_mul, sec8t84FPRaw_one, hy, hy_cube]
  have hy3 : y₀ ^ 3 = 1 := by rw [pow_three]; exact hcube0
  have hy_ord : orderOf y₀ = 3 := orderOf_eq_prime hy3 hy0_ne
  have hy_inv : y₀⁻¹ = y₀ * y₀ := inv_eq_of_mul_eq_one_right hcube0
  have hraw_inv : sec8t84FPRaw F y₀⁻¹ = mulE y y := by
    rw [hy_inv, sec8t84FPRaw_mul, hy]
  have hfwd : ∀ x : Sec8T84FPM0 F, sec8t84FPRaw F x ∈ Jl →
      sec8t84FPRaw F (y₀ * x * y₀⁻¹) ∈ Jl := by
    intro x hx
    have h1 : sec8t84FPRaw F (y₀ * x * y₀⁻¹) =
        mulE (mulE y (sec8t84FPRaw F x)) (mulE y y) := by
      simp only [sec8t84FPRaw_mul, hraw_inv, hy]
    rw [h1]
    exact hyJ _ hx
  have hy_norm : y₀ ∈ normalizer
      ((sec8t84FPJ0 F G : Subgroup (Sec8T84FPM0 F)) : Set (Sec8T84FPM0 F)) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hfwd h hh
    · intro hh
      have hk : sec8t84FPRaw F (y₀ * h * y₀⁻¹) ∈ Jl := hh
      have h2 : sec8t84FPRaw F (y₀ * (y₀ * (y₀ * h * y₀⁻¹) * y₀⁻¹) * y₀⁻¹) ∈ Jl :=
        hfwd (y₀ * (y₀ * h * y₀⁻¹) * y₀⁻¹) (hfwd (y₀ * h * y₀⁻¹) hk)
      rw [t84_conj_cube y₀ h hy3] at h2
      exact h2
  have hyfix0 : ∀ u ∈ sec8t84FPJ0 F G, y₀ * u = u * y₀ → u = 1 := by
    intro u hu hcomm
    have hcu : commE y (sec8t84FPRaw F u) := by
      rw [← hy]
      exact (sec8t84FPRaw_commE_iff F y₀ u).mpr hcomm
    exact (sec8t84FPRaw_eq_oneE_iff F u).mp (hyfix (sec8t84FPRaw F u) hu hcu)
  have hs0_ne : s₀ ≠ 1 := fun h =>
    hsJ (by rw [← hs, h, sec8t84FPRaw_one]; exact sec8t84_oneE_Jl G)
  have hssq0 : s₀ * s₀ = 1 :=
    (sec8t84FPRaw_mul_self_iff F s₀).mp (by rw [hs]; exact hs_sq)
  have hs_ord : orderOf s₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hssq0) hs0_ne
  have hsxy : s₀ * y₀ * s₀ = y₀ * y₀ := by
    apply sec8t84FPRaw_injective F
    simp only [sec8t84FPRaw_mul, hs, hy, hs_sy]
  have hs_inv : s₀ * y₀ * s₀⁻¹ = y₀⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hssq0, hsxy, ← hy_inv]
  have hsP0 : s₀ ∈ sec8t84FPP0 F G := by
    change sec8t84FPRaw F s₀ ∈ P0l
    rw [hs]
    exact hsP
  have hsJ0 : s₀ ∉ sec8t84FPJ0 F G := by
    intro hJ
    have : s ∈ Jl := by
      rw [← hs]
      exact hJ
    exact hsJ this
  have hJP : sec8t84FPJ0 F G ≤ sec8t84FPP0 F G :=
    sec8t84FPOfList_le F (sec8t84_oneE_Jl G) G.j.2.2.2 G.p0.2.2.1 G.p0.2.2.2.2 G.j.2.2.1
  have hP0_eq : sec8t84FPP0 F G = zpowers s₀ ⊔ sec8t84FPJ0 F G := by
    apply le_antisymm
    · intro p hp
      rcases hsplit (sec8t84FPRaw F p) hp with hpJ | hpJ
      · exact Subgroup.mem_sup_right hpJ
      · have hsp : sec8t84FPRaw F (s₀ * p) ∈ Jl := by
          rw [sec8t84FPRaw_mul, hs]
          exact hpJ
        have hmem : s₀ * (s₀ * p) ∈ zpowers s₀ ⊔ sec8t84FPJ0 F G :=
          Subgroup.mul_mem_sup (Subgroup.mem_zpowers s₀) hsp
        rwa [show s₀ * (s₀ * p) = p by rw [← mul_assoc, hssq0, one_mul]] at hmem
    · apply sup_le
      · exact Subgroup.zpowers_le.mpr hsP0
      · exact hJP
  exact ⟨y₀, hy_ord, hy_norm, hyfix0, s₀, hsP0, hsJ0, hs_ord, hs_inv, hP0_eq⟩

end CFSG.OddStandard.SmallF3.Omega
