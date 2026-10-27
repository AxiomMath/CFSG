module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OSteps

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace E3S3O

section Cit3


theorem Ctx.secImg_core_le {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {J : Subgroup Y} {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd}
    {S' : Sylow 2 Y} {R' T W : Subgroup Y} (h : Ctx n R S t J u L Rd Sd S' R' T W) :
    secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore R) ≤ orbW Rd (u * t) := by
  have hΦR := (TightLargeHypR.typeRFam h.std.large).secFam (x := u * t)
  have hcl := hΦR.hyp.conjInvariant
  have hKb := secImg_mem h.std.xMem_K
  have hcomm := Vtx.commute_conj_of_not_conj h.thm4 hΦR secQuot_oddCore_eq_bot
    h.std.natCard_secQuot_lt hKb
  obtain ⟨g, hg⟩ := h.conj
  have hgG : g ∈ omegaGen (secFam (CoreAssembly.conjClass (tightCore Rd)) (u * t)) := by
    rw [omegaGen_secFam]
    exact Subgroup.mem_top g
  obtain ⟨k, hk, ek⟩ := Vtx.exists_orbGrp_conj hcl hKb hcomm hgG
  rw [← hg, ek]
  exact Vtx.conjSub_le_orbGrp _ ⟨k, Vtx.orbGrp_le hcl hKb hk⟩

theorem stepW_proved {n : ℕ} : StepW n := by
  intro Y _ _ R S t J u L Rd Sd S' R' T W h
  classical
  have hs := h.std
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  set Φ := secFam Ω (u * t) with hΦdef
  set X := secOrb Ω K (u * t) with hXdef
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (u * t))) with hπdef
  have hR := TightLargeHypR.typeRFam hs.large
  have hΦR : TypeRFam 3 Φ := hR.secFam
  have hcl := hΦR.hyp.conjInvariant
  have hO : classicalInvolutionOddCore (SecQuot Ω (u * t)) = ⊥ := secQuot_oddCore_eq_bot
  have hn : Nat.card (SecQuot Ω (u * t)) < n := hs.natCard_secQuot_lt
  have hKb : secImg Ω (u * t) K ∈ Φ := secImg_mem hs.xMem_K
  have huY := mem_layerY_of_isUniqueInvolution hR hs.xMem_K hs.hz
  have htY := mem_layerY_of_isUniqueInvolution hR hs.xMem_J hs.ht
  have hub := isUniqueInvolution_secImg hR hs.xMem_K hs.hz
  have htb := isUniqueInvolution_secImg hR hs.xMem_J hs.ht
  have hcomm := Vtx.commute_conj_of_not_conj h.thm4 hΦR hO hn hKb
  obtain ⟨g, hg⟩ := h.conj
  have hgG : g ∈ omegaGen Φ := by
    rw [omegaGen_secFam]
    exact Subgroup.mem_top g
  obtain ⟨k, hk, ek⟩ := Vtx.exists_orbGrp_conj hcl hKb hcomm hgG
  have hKX : secImg Ω (u * t) K ≤ X := Vtx.le_orbGrp _
  have hJX : secImg Ω (u * t) (tightCore R) ≤ X := by
    rw [← hg, ek]
    exact Vtx.conjSub_le_orbGrp _ ⟨k, Vtx.orbGrp_le hcl hKb hk⟩
  have hΦX : TypeRFam 3 (restrictFamily Φ X) := hΦR.restrict X
  have hOX : classicalInvolutionOddCore ↥X = ⊥ :=
    oddCore_eq_bot_of_isSubnormal (Vtx.isSubnormal_orbGrp hcl hKb) hO
  have hA : (secImg Ω (u * t) K).subgroupOf X ∈ restrictFamily Φ X := ⟨_, hKb, hKX, rfl⟩
  have hB : (secImg Ω (u * t) (tightCore R)).subgroupOf X ∈ restrictFamily Φ X :=
    ⟨_, secImg_mem hs.xMem_J, hJX, rfl⟩
  have hgenA : (⨆ c : ↥X, conjSub c ((secImg Ω (u * t) K).subgroupOf X)) = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e2 : ∀ c : ↥X, (conjSub c ((secImg Ω (u * t) K).subgroupOf X)).map X.subtype =
        conjSub (c : SecQuot Ω (u * t)) (secImg Ω (u * t) K) := by
      intro c
      rw [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le]
      exact Vtx.conjSub_le_orbGrp _ ⟨(c : SecQuot Ω (u * t)), Vtx.orbGrp_le hcl hKb c.2⟩
    simp_rw [e2]
    exact (Vtx.orbGrp_eq_iSup hcl hKb hcomm).symm
  set x : ↥X := ⟨π ⟨u, huY⟩, hKX hub.mem⟩ with hxdef
  set x' : ↥X := ⟨π ⟨t, htY⟩, hJX htb.mem⟩ with hx'def
  have hx : IsUniqueInvolution ((secImg Ω (u * t) K).subgroupOf X) x :=
    isUniqueInvolution_subgroupOf hub hKX
  have hx' : IsUniqueInvolution ((secImg Ω (u * t) (tightCore R)).subgroupOf X) x' :=
    isUniqueInvolution_subgroupOf htb hJX
  have hcenZ := hs.mk_mul_mk_mem_center huY htY
  have hcen : x * x' ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcenZ (c : SecQuot Ω (u * t)))
  have hne : x ≠ x' := by
    intro e
    have hJK := hs.secImg_J_mem_omegaNbr.2.1
    have htw := hΦX.noTwins _ hA _ ⟨hB, x, hx, e ▸ hx'⟩
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hJX, inf_eq_left.mpr hKX] at htw
    exact hJK htw
  have haY : u * t ∈ layerY Ω (u * t) := (layerY Ω (u * t)).mul_mem huY htY
  have hxx' : ((x * x' : ↥X) : SecQuot Ω (u * t)) = π ⟨u * t, haY⟩ := by
    show π ⟨u, huY⟩ * π ⟨t, htY⟩ = π ⟨u * t, haY⟩
    rw [← map_mul]
    rfl
  have hnO2 : ¬ ∃ P : Subgroup ↥X, P.Normal ∧ IsPGroup 2 ↥P ∧ x ∈ P := by
    rintro ⟨P, hPn, hP2, hxP⟩
    refine h.notO2 ⟨P, hPn, hP2, fun c hcz => ?_⟩
    obtain ⟨w, hw, hwc⟩ := hcz
    have hw' : (w : Y) ∈ Subgroup.zpowers u := Subgroup.mem_subgroupOf.mp hw
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw'
    have hwm : w = (⟨u, huY⟩ : ↥(layerY Ω (u * t))) ^ m := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, ← hm]
    have hcm : c = x ^ m := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, ← hwc, hwm, map_zpow]
    rw [hcm]
    exact P.zpow_mem hxP m
  refine ⟨x, x', ⟨hΦX, hOX, hA, ⟨⟨k, hk⟩, ?_⟩, hx, hx', hne, hcen, hgenA, hnO2⟩, ?_⟩
  · show conjSub _ _ = _
    rw [conjSub_subgroupOf]
    congr 1
    rw [← ek, hg]
  rintro ⟨N, hNn, -, -, hNc, hom⟩
  refine ⟨N, hNn, ?_, hom⟩
  ext c
  rw [hNc]
  constructor
  · rintro ⟨w, hw, hwc⟩
    have hw' : (w : Y) ∈ Subgroup.zpowers (u * t) := Subgroup.mem_subgroupOf.mp hw
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw'
    have hwm : w = (⟨u * t, haY⟩ : ↥(layerY Ω (u * t))) ^ m := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, ← hm]
    have hcm : c = (x * x') ^ m := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, hxx', ← hwc, hwm, map_zpow]
    rw [hcm]
    exact Subgroup.zpow_mem_zpowers _ m
  · intro hc
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine ⟨(⟨u * t, haY⟩ : ↥(layerY Ω (u * t))) ^ m, ?_, ?_⟩
    · show (⟨u * t, haY⟩ : ↥(layerY Ω (u * t))) ^ m ∈
        (Subgroup.zpowers (u * t)).subgroupOf (layerY Ω (u * t))
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_zpow]
      exact Subgroup.zpow_mem_zpowers _ m
    · rw [map_zpow, Subgroup.coe_zpow, hxx']

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
