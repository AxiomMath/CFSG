module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31OutA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_coset_invol_conj (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) {t'' : G} (ht : ActsAs L t'' s.fr'.σ)
    (ht2 : t'' ^ 2 = 1) {l : G} (hl : l ∈ L) (hw : (t'' * l) ^ 2 = 1) :
    ∃ l₂ ∈ L, t'' * l = l₂ * t'' * l₂⁻¹ := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  set il : MulAut (L ⧸ center L) :=
    MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L)) with hil_def
  set α : MulAut (L ⧸ center L) := s.fr'.σ * il with hα_def
  have hil_mem : il ∈ innerAut (L ⧸ center L) := by
    rw [innerAut, MonoidHom.mem_range]
    exact ⟨QuotientGroup.mk (⟨l, hl⟩ : ↥L), hil_def.symm⟩
  have hw_acts : ActsAs L (t'' * l) α := by
    rw [hα_def, hil_def]
    exact actsAs_mul L ht (actsAs_of_mem L hl)
  have hww : (t'' * l) * (t'' * l) = 1 := by
    rw [← pow_two]
    exact hw
  have hα2 : α ^ 2 = 1 := by
    rw [pow_two]
    exact actsAs_unique L (actsAs_mul L hw_acts hw_acts) (by rw [hww]; exact actsAs_one L)
  have hα_out : α ∉ innerAut (L ⧸ center L) := by
    intro hαin
    have hσ_eq : s.fr'.σ = α * il⁻¹ := by rw [hα_def]; group
    apply frame_sigma_not_mem_inner s.fr' s.facts.1 hOut
    rw [hσ_eq]
    exact mul_mem hαin (inv_mem hil_mem)
  obtain ⟨i, hi_mem, hi_conj⟩ := frame_outer_invol_conj s.fr' s.facts hOut hα2 hα_out
  rw [innerAut] at hi_mem
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hi_mem
  obtain ⟨l₁, hl₁⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
  set il₁ : MulAut (L ⧸ center L) :=
    MulAut.conj (QuotientGroup.mk (l₁ : ↥L)) with hil₁_def
  have hq' : q = (l₁ : L ⧸ center L) := by
    rw [← hl₁]
    exact QuotientGroup.mk'_apply (Subgroup.center ↥L) l₁
  have hi_eq : i = il₁ := by
    rw [hil₁_def, ← hq, hq']
  have h_l₁_acts : ActsAs L (l₁ : G) il₁ := by
    rw [hil₁_def]
    exact actsAs_of_mem L l₁.2
  have hconj_acts : ActsAs L ((l₁ : G) * (t'' * l) * (l₁ : G)⁻¹) s.fr'.σ := by
    have h1 : ActsAs L ((l₁ : G) * (t'' * l) * (l₁ : G)⁻¹) (il₁ * α * il₁⁻¹) :=
      actsAs_mul L (actsAs_mul L h_l₁_acts hw_acts) (actsAs_inv L h_l₁_acts)
    rw [show il₁ * α * il₁⁻¹ = s.fr'.σ from by rw [← hi_eq]; exact hi_conj] at h1
    exact h1
  set c : G := ((l₁ : G) * (t'' * l) * (l₁ : G)⁻¹) * t''⁻¹ with hc_def
  have hc_acts : ActsAs L c (1 : MulAut (L ⧸ center L)) := by
    have h1 : ActsAs L c (s.fr'.σ * s.fr'.σ⁻¹) := by
      rw [hc_def]
      exact actsAs_mul L hconj_acts (actsAs_inv L ht)
    simpa using h1
  have hc_cent : c ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hc_acts
  have hn : t'' ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L ht
  have hc_L : c ∈ L := by
    have hd : t'' * (l * (l₁ : G)⁻¹) * t''⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hn (l * (l₁ : G)⁻¹)).mp
        (L.mul_mem hl (L.inv_mem l₁.2))
    rw [hc_def]
    rw [show ((l₁ : G) * (t'' * l) * (l₁ : G)⁻¹) * t''⁻¹
          = (l₁ : G) * (t'' * (l * (l₁ : G)⁻¹) * t''⁻¹) by group]
    exact L.mul_mem l₁.2 hd
  have hc_center : (⟨c, hc_L⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc_cent) (y : G) y.2)
  have hm_dvd : orderOf c ∣ Nat.card ↥(center ↥L) := by
    have h := Subgroup.orderOf_dvd_natCard (center ↥L) hc_center
    simpa using h
  have hm_odd : Odd (orderOf c) := hZ.of_dvd_nat hm_dvd
  obtain ⟨k, hk⟩ := hm_odd
  set ξ : G := c ^ (k + 1) with hξ_def
  have hξ_L : ξ ∈ L := by rw [hξ_def]; exact L.pow_mem hc_L (k + 1)
  have hξ_sq : ξ ^ 2 = c := by
    rw [hξ_def, ← pow_mul]
    have h1 : (k + 1) * 2 = orderOf c + 1 := by omega
    rw [h1, pow_succ, pow_orderOf_eq_one, one_mul]
  have hct_eq : c * t'' = (l₁ : G) * (t'' * l) * (l₁ : G)⁻¹ := by
    rw [hc_def]; group
  have hconj_sq : ((l₁ : G) * (t'' * l) * (l₁ : G)⁻¹) ^ 2
      = (l₁ : G) * (t'' * l) ^ 2 * (l₁ : G)⁻¹ := by
    rw [← MulAut.conj_apply (l₁ : G) (t'' * l), ← map_pow, MulAut.conj_apply]
  have hct2 : (c * t'') ^ 2 = 1 := by
    rw [hct_eq, hconj_sq, hw]
    group
  have ht2mul : t'' * t'' = 1 := by simpa [pow_two] using ht2
  have ht2inv : t''⁻¹ = t'' := inv_eq_of_mul_eq_one_left ht2mul
  have ht''_c : t'' * c * t''⁻¹ = c⁻¹ := by
    have h2 : t'' * c * t'' = c⁻¹ := by
      have h : c * (t'' * c * t'') = c * c⁻¹ := by
        calc c * (t'' * c * t'') = (c * t'') * (c * t'') := by group
          _ = (c * t'') ^ 2 := by rw [pow_two]
          _ = 1 := hct2
          _ = c * c⁻¹ := by rw [mul_inv_cancel]
      exact mul_left_cancel h
    rw [ht2inv]
    exact h2
  have hconj_c : MulAut.conj t'' c = c⁻¹ := by
    rw [MulAut.conj_apply]; exact ht''_c
  have ht''_ξ : t'' * ξ * t''⁻¹ = ξ⁻¹ := by
    rw [hξ_def, ← MulAut.conj_apply, map_pow, hconj_c, inv_pow]
  have hξt'' : ξ * t'' * ξ⁻¹ = c * t'' := by
    have h1 : t'' * ξ⁻¹ = ξ * t'' := by
      have h : t'' * ξ⁻¹ * t''⁻¹ = ξ := by
        rw [mul_assoc]
        have := congrArg Inv.inv ht''_ξ
        simpa only [mul_inv_rev, inv_inv] using this
      calc t'' * ξ⁻¹ = t'' * ξ⁻¹ * 1 := by rw [mul_one]
        _ = t'' * ξ⁻¹ * (t''⁻¹ * t'') := by rw [inv_mul_cancel]
        _ = (t'' * ξ⁻¹ * t''⁻¹) * t'' := by group
        _ = ξ * t'' := by rw [h]
    calc ξ * t'' * ξ⁻¹ = ξ * (t'' * ξ⁻¹) := by group
      _ = ξ * (ξ * t'') := by rw [h1]
      _ = (ξ * ξ) * t'' := by group
      _ = c * t'' := by rw [show ξ * ξ = c by rw [← pow_two, hξ_sq]]
  refine ⟨(l₁ : G)⁻¹ * ξ, L.mul_mem (L.inv_mem l₁.2) hξ_L, ?_⟩
  rw [show ((l₁ : G)⁻¹ * ξ) * t'' * ((l₁ : G)⁻¹ * ξ)⁻¹
        = (l₁ : G)⁻¹ * (ξ * t'' * ξ⁻¹) * (l₁ : G) by group]
  rw [hξt'', hct_eq]
  group

end CFSG.OddStandard.HigherRank.YamadaG23
