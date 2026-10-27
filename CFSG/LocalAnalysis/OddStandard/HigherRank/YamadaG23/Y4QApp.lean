module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4QLem
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Csq
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Cover

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private lemma y4_B_subgroupOf_C2_normal (c : Ctx4 s e) :
    ((s.fr.B).subgroupOf s.C₂).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((f3_C₂_le_X c.toF33).trans (f3_X_le_normB c.toF33))

private theorem y4_C2_quot_elemab (c : Ctx4 s e)
    [((s.fr.B).subgroupOf s.C₂).Normal] :
    ∀ q q' : (↥s.C₂ ⧸ (s.fr.B).subgroupOf s.C₂), q * q' = q' * q ∧ q * q = 1 := by
  have hH : F33Hyp s e := c.toF33
  have hBleC2 : s.fr.B ≤ s.C₂ :=
    (le_sup_left : s.fr.B ≤ f3P s).trans (f3_P_le_C₂ hH)
  have htC₂ : s.t ∈ s.C₂ :=
    f3_P_le_C₂ hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  let π : ↥s.C₂ →* (↥s.C₂ ⧸ (s.fr.B).subgroupOf s.C₂) :=
    QuotientGroup.mk' ((s.fr.B).subgroupOf s.C₂)
  obtain ⟨k, hk⟩ := y52_exists_K hH
  obtain ⟨y, hyC, hyphi, hy2B⟩ := y4_exists_c_sq c
  have hyP : y ∉ f3P s := fun hyP =>
    hyphi ((f3_phi_eq_one hH y (f3_C₂_le_Y hH hyC)).mpr (f3_P_le_X0 s hyP))
  have hkL : k ∈ L := hk.mem.1
  have hkN : k ∈ f3N s := ⟨s3_L_le_H s hH.hS hkL, hk.mem.2⟩
  have hkX : k ∈ s.X := f3_N_le_X s hkN
  have hk2X : k ^ 2 ∈ s.X := f3_N_le_X s ((f3N s).pow_mem hkN 2)
  have hkyC : k * y * k⁻¹ ∈ s.C₂ := f3_C₂_normal hH k hkX y hyC
  have hk2yC : k ^ 2 * y * (k ^ 2)⁻¹ ∈ s.C₂ := f3_C₂_normal hH (k ^ 2) hk2X y hyC
  have hsq_invol : ∀ (z : G) (hz : z ∈ s.C₂), z * z ∈ s.fr.B →
      π ⟨z, hz⟩ * π ⟨z, hz⟩ = 1 := by
    intro z hz hzsq
    rw [← map_mul π]
    exact (QuotientGroup.eq_one_iff (N := (s.fr.B).subgroupOf s.C₂) _).mpr
      (Subgroup.mem_subgroupOf.mpr hzsq)
  have hpiP : ∀ (z : G) (hz : z ∈ s.C₂), z ∈ f3P s →
      π ⟨z, hz⟩ = 1 ∨ π ⟨z, hz⟩ = π ⟨s.t, htC₂⟩ := by
    intro z hz hzP
    rcases f3_mem_P z hzP with hzB | ⟨b, hbB, hzb⟩
    · left
      exact (QuotientGroup.eq_one_iff (N := (s.fr.B).subgroupOf s.C₂) _).mpr
        (Subgroup.mem_subgroupOf.mpr hzB)
    · right
      have hb1 : π (⟨b, hBleC2 hbB⟩ : ↥s.C₂) = 1 :=
        (QuotientGroup.eq_one_iff (N := (s.fr.B).subgroupOf s.C₂)
          (⟨b, hBleC2 hbB⟩ : ↥s.C₂)).mpr (Subgroup.mem_subgroupOf.mpr hbB)
      have hzb' : (⟨z, hz⟩ : ↥s.C₂) = ⟨b, hBleC2 hbB⟩ * ⟨s.t, htC₂⟩ := by
        apply Subtype.ext
        show z = b * s.t
        exact hzb
      rw [hzb', map_mul π (⟨b, hBleC2 hbB⟩ : ↥s.C₂) ⟨s.t, htC₂⟩, hb1, one_mul]
  have hy_sq : y * y ∈ s.fr.B := by rw [← pow_two]; exact hy2B
  have hy1_sq : (k * y * k⁻¹) * (k * y * k⁻¹) ∈ s.fr.B := by
    have h1 : k * (y * y) * k⁻¹ ∈ s.fr.B :=
      (Subgroup.mem_set_normalizer_iff.mp hk.mem.2 (y * y)).mp hy_sq
    rwa [show (k * y * k⁻¹) * (k * y * k⁻¹) = k * (y * y) * k⁻¹ by group]
  have hk2norm : k ^ 2 ∈ normalizer (s.fr.B : Set G) :=
    (Subgroup.normalizer (s.fr.B : Set G)).pow_mem hk.mem.2 2
  have hy2_sq : (k ^ 2 * y * (k ^ 2)⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) ∈ s.fr.B := by
    have h1 : k ^ 2 * (y * y) * (k ^ 2)⁻¹ ∈ s.fr.B :=
      (Subgroup.mem_set_normalizer_iff.mp hk2norm (y * y)).mp hy_sq
    rwa [show (k ^ 2 * y * (k ^ 2)⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) =
      k ^ 2 * (y * y) * (k ^ 2)⁻¹ by group]
  have ha : π ⟨y, hyC⟩ * π ⟨y, hyC⟩ = 1 := hsq_invol y hyC hy_sq
  have hb : π ⟨k * y * k⁻¹, hkyC⟩ * π ⟨k * y * k⁻¹, hkyC⟩ = 1 :=
    hsq_invol (k * y * k⁻¹) hkyC hy1_sq
  have hc : π ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩ * π ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩ = 1 :=
    hsq_invol (k ^ 2 * y * (k ^ 2)⁻¹) hk2yC hy2_sq
  have htt : s.t * s.t = 1 := by
    rw [← pow_two, ← s.t_order]; exact pow_orderOf_eq_one s.t
  have ht : π ⟨s.t, htC₂⟩ * π ⟨s.t, htC₂⟩ = 1 := by
    rw [← map_mul π]
    have h1 : (⟨s.t, htC₂⟩ * ⟨s.t, htC₂⟩ : ↥s.C₂) = 1 := by
      apply Subtype.ext
      show s.t * s.t = (1 : G)
      exact htt
    rw [h1, map_one]
  have htc : ∀ q : (↥s.C₂ ⧸ (s.fr.B).subgroupOf s.C₂),
      q * π ⟨s.t, htC₂⟩ = π ⟨s.t, htC₂⟩ * q := by
    intro q
    obtain ⟨xv, rfl⟩ := QuotientGroup.mk'_surjective ((s.fr.B).subgroupOf s.C₂) q
    have hmemN : ⁅xv, ⟨s.t, htC₂⟩⁆ ∈ (s.fr.B).subgroupOf s.C₂ := by
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((⁅xv, ⟨s.t, htC₂⟩⁆ : ↥s.C₂) : G) = ⁅(xv : G), s.t⁆ := by
        simp [commutatorElement_def]
      rw [hcoe]
      exact (Subgroup.mem_inf.mp (y4_comm_t_mem_V c xv.2)).1
    have h1 : ⁅π xv, π ⟨s.t, htC₂⟩⁆ = 1 := by
      have h2 : π ⁅xv, ⟨s.t, htC₂⟩⁆ = 1 :=
        (QuotientGroup.eq_one_iff (N := (s.fr.B).subgroupOf s.C₂) _).mpr hmemN
      rwa [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hprodC : y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) ∈ s.C₂ :=
    s.C₂.mul_mem (s.C₂.mul_mem hyC hkyC) hk2yC
  have hprodP : y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) ∈ f3P s :=
    y52_cover_prod hH hk hyC hyP
  have hpv_eq : π ⟨y, hyC⟩ * π ⟨k * y * k⁻¹, hkyC⟩ *
      π ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩ =
      π ⟨y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹), hprodC⟩ := by
    have hD : (⟨y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹), hprodC⟩ : ↥s.C₂) =
        (⟨y, hyC⟩ * ⟨k * y * k⁻¹, hkyC⟩) * ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩ :=
      Subtype.ext rfl
    rw [hD]
    exact ((map_mul π (⟨y, hyC⟩ * ⟨k * y * k⁻¹, hkyC⟩)
        ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩).trans
      (congrArg (fun z => z * π ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩)
        (map_mul π ⟨y, hyC⟩ ⟨k * y * k⁻¹, hkyC⟩))).symm
  have habc : π ⟨y, hyC⟩ * π ⟨k * y * k⁻¹, hkyC⟩ *
      π ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩ = 1 ∨
      π ⟨y, hyC⟩ * π ⟨k * y * k⁻¹, hkyC⟩ *
        π ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩ = π ⟨s.t, htC₂⟩ := by
    rcases hpiP _ hprodC hprodP with h1 | h1
    · left; rw [hpv_eq, h1]
    · right; rw [hpv_eq, h1]
  have hall : ∀ q : (↥s.C₂ ⧸ (s.fr.B).subgroupOf s.C₂),
      ∃ p : (↥s.C₂ ⧸ (s.fr.B).subgroupOf s.C₂),
        (p = 1 ∨ p = π ⟨s.t, htC₂⟩) ∧
          (q = p ∨ q = p * π ⟨y, hyC⟩ ∨
            q = p * π ⟨k * y * k⁻¹, hkyC⟩ ∨
            q = p * π ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩) := by
    intro q
    obtain ⟨xv, rfl⟩ := QuotientGroup.mk'_surjective ((s.fr.B).subgroupOf s.C₂) q
    obtain ⟨p₀, hp₀P, hcase⟩ := y52_cover hH hk hyC hyP (xv : G) xv.2
    have hp₀C : p₀ ∈ s.C₂ := f3_P_le_C₂ hH hp₀P
    rcases hpiP p₀ hp₀C hp₀P with hp0 | hp0
    · refine ⟨1, Or.inl rfl, ?_⟩
      rcases hcase with h | h | h | h
      · left
        rw [show xv = (⟨p₀, hp₀C⟩ : ↥s.C₂) from Subtype.ext h, hp0]
      · right; left
        rw [show xv = (⟨p₀, hp₀C⟩ : ↥s.C₂) * ⟨y, hyC⟩ from Subtype.ext (by simpa using h),
          map_mul π (⟨p₀, hp₀C⟩ : ↥s.C₂) ⟨y, hyC⟩, hp0, one_mul]
      · right; right; left
        rw [show xv = (⟨p₀, hp₀C⟩ : ↥s.C₂) * ⟨k * y * k⁻¹, hkyC⟩ from
            Subtype.ext (by simpa using h),
          map_mul π (⟨p₀, hp₀C⟩ : ↥s.C₂) ⟨k * y * k⁻¹, hkyC⟩, hp0, one_mul]
      · right; right; right
        rw [show xv = (⟨p₀, hp₀C⟩ : ↥s.C₂) * ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩ from
            Subtype.ext (by simpa using h),
          map_mul π (⟨p₀, hp₀C⟩ : ↥s.C₂) ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩, hp0, one_mul]
    · refine ⟨π ⟨s.t, htC₂⟩, Or.inr rfl, ?_⟩
      rcases hcase with h | h | h | h
      · left
        rw [show xv = (⟨p₀, hp₀C⟩ : ↥s.C₂) from Subtype.ext h, hp0]
      · right; left
        rw [show xv = (⟨p₀, hp₀C⟩ : ↥s.C₂) * ⟨y, hyC⟩ from Subtype.ext (by simpa using h),
          map_mul π (⟨p₀, hp₀C⟩ : ↥s.C₂) ⟨y, hyC⟩, hp0]
      · right; right; left
        rw [show xv = (⟨p₀, hp₀C⟩ : ↥s.C₂) * ⟨k * y * k⁻¹, hkyC⟩ from
            Subtype.ext (by simpa using h),
          map_mul π (⟨p₀, hp₀C⟩ : ↥s.C₂) ⟨k * y * k⁻¹, hkyC⟩, hp0]
      · right; right; right
        rw [show xv = (⟨p₀, hp₀C⟩ : ↥s.C₂) * ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩ from
            Subtype.ext (by simpa using h),
          map_mul π (⟨p₀, hp₀C⟩ : ↥s.C₂) ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩, hp0]
  exact y4_elemab_of_orbit (t := π ⟨s.t, htC₂⟩) (a := π ⟨y, hyC⟩)
    (b := π ⟨k * y * k⁻¹, hkyC⟩) (c := π ⟨k ^ 2 * y * (k ^ 2)⁻¹, hk2yC⟩)
    ht htc ha hb hc habc hall

theorem y4_C2_comm (c : Ctx4 s e) : ∀ x ∈ s.C₂, ∀ y ∈ s.C₂, ⁅x, y⁆ ∈ s.fr.B := by
  haveI hN := y4_B_subgroupOf_C2_normal c
  have hmain := y4_C2_quot_elemab c
  intro x hx y hy
  let π : ↥s.C₂ →* (↥s.C₂ ⧸ (s.fr.B).subgroupOf s.C₂) :=
    QuotientGroup.mk' ((s.fr.B).subgroupOf s.C₂)
  have hq : π (⟨x, hx⟩ * ⟨y, hy⟩) = π (⟨y, hy⟩ * ⟨x, hx⟩) := by
    rw [map_mul π, map_mul π]
    exact (hmain (π ⟨x, hx⟩) (π ⟨y, hy⟩)).1
  have hmem : (⟨x, hx⟩ * ⟨y, hy⟩) / (⟨y, hy⟩ * ⟨x, hx⟩) ∈
      (s.fr.B).subgroupOf s.C₂ :=
    (QuotientGroup.eq_iff_div_mem (N := (s.fr.B).subgroupOf s.C₂)).mp hq
  have hcoe : (((⟨x, hx⟩ * ⟨y, hy⟩) / (⟨y, hy⟩ * ⟨x, hx⟩) : ↥s.C₂) : G) = ⁅x, y⁆ := by
    rw [commutatorElement_def, div_eq_mul_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hthis : (((⟨x, hx⟩ * ⟨y, hy⟩) / (⟨y, hy⟩ * ⟨x, hx⟩) : ↥s.C₂) : G) ∈ s.fr.B :=
    Subgroup.mem_subgroupOf.mp hmem
  rwa [hcoe] at hthis

end CFSG.OddStandard.HigherRank.YamadaG23
