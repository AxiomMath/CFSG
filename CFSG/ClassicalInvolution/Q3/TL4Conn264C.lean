module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264A
public import CFSG.ClassicalInvolution.Q3.TL4Conn26YS
public import CFSG.ClassicalInvolution.Q3.TL4E3TQQuot
public import CFSG.ClassicalInvolution.Q3.TL4E3TQSect

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem twinE4_of_surjective {Y Y' : Type} [Group Y] [Group Y'] (g : Y →* Y')
    (hg : Function.Surjective g) (hk : IsPGroup 2 ↥g.ker) (h : TwinE4 Y') : TwinE4 Y := by
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h
  refine ⟨Q, inferInstance, f.comp g, hfs.comp hg, ?_, hQ⟩
  rw [← MonoidHom.comap_ker]
  exact hf2.comap_of_ker_isPGroup g hk

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.secTwinOmega_or_twinE4 (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetBelow n) (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hc : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hE2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z) :
    TwinE4 ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)) ∨
      SecTwinOmega (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  set Φ := secFam Ω (z * t) with hΦdef
  set X := secOrb Ω K (z * t) with hXdef
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) with hπdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ : TypeRFam 3 Φ := h.secFam
  have hcl := hΦ.hyp.conjInvariant
  have hO : classicalInvolutionOddCore (SecQuot Ω (z * t)) = ⊥ := secQuot_oddCore_eq_bot
  have hn : Nat.card (SecQuot Ω (z * t)) < n := hs.natCard_secQuot_lt
  have hgen : omegaGen Φ = ⊤ := omegaGen_secFam
  have hKb : secImg Ω (z * t) K ∈ Φ := secImg_mem hs.xMem_K
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have htY := mem_layerY_of_isUniqueInvolution h hs.xMem_J hs.ht
  have hzb := isUniqueInvolution_secImg h hs.xMem_K hs.hz
  have htb := isUniqueInvolution_secImg h hs.xMem_J hs.ht
  have hcomm := Vtx.commute_conj_of_not_conj h4 hΦ hO hn hKb
  obtain ⟨g, hg⟩ := hc
  have hgG : g ∈ omegaGen Φ := by
    rw [hgen]
    exact Subgroup.mem_top g
  obtain ⟨k, hk, ek⟩ := Vtx.exists_orbGrp_conj hcl hKb hcomm hgG
  have hKX : secImg Ω (z * t) K ≤ X := Vtx.le_orbGrp _
  have hJX : secImg Ω (z * t) J ≤ X := by
    rw [← hg, ek]
    exact Vtx.conjSub_le_orbGrp _ ⟨k, Vtx.orbGrp_le hcl hKb hk⟩
  have hΦX : TypeRFam 3 (restrictFamily Φ X) := hΦ.restrict X
  have hOX : classicalInvolutionOddCore ↥X = ⊥ :=
    oddCore_eq_bot_of_isSubnormal (Vtx.isSubnormal_orbGrp hcl hKb) hO
  have hAX : ∀ L ∈ restrictFamily Φ X, AEmpty (restrictFamily Φ X) L :=
    fun L hL => aEmpty_of_noTwins hΦX.hyp hL (hΦX.noTwins L hL)
  have hA : (secImg Ω (z * t) K).subgroupOf X ∈ restrictFamily Φ X := ⟨_, hKb, hKX, rfl⟩
  have hgenA : (⨆ c : ↥X, conjSub c ((secImg Ω (z * t) K).subgroupOf X)) = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e2 : ∀ c : ↥X, (conjSub c ((secImg Ω (z * t) K).subgroupOf X)).map X.subtype =
        conjSub (c : SecQuot Ω (z * t)) (secImg Ω (z * t) K) := by
      intro c
      rw [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le]
      exact Vtx.conjSub_le_orbGrp _ ⟨(c : SecQuot Ω (z * t)), Vtx.orbGrp_le hcl hKb c.2⟩
    simp_rw [e2]
    exact (Vtx.orbGrp_eq_iSup hcl hKb hcomm).symm
  have hB : (secImg Ω (z * t) J).subgroupOf X ∈
      omegaNbr (restrictFamily Φ X) ((secImg Ω (z * t) K).subgroupOf X) := by
    obtain ⟨hJΦ, hne, T', hT', hT'J, hT'N⟩ := hs.secImg_J_mem_omegaNbr
    have hT'syl : IsSylow2In T' (secImg Ω (z * t) J) :=
      Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ.hyp hJΦ hT' hT'J
    exact ⟨⟨_, hJΦ, hJX, rfl⟩, subgroupOf_ne_of_ne hKX hJX hne, T'.subgroupOf X,
      mem_RSet_restrict hJΦ hJX hT'syl,
      fun y hy => Subgroup.mem_subgroupOf.mpr (hT'J (Subgroup.mem_subgroupOf.mp hy)),
      fun y hy => (mem_normalizer_subgroupOf_iff hKX).mp (hT'N (Subgroup.mem_subgroupOf.mp hy))⟩
  have hAB : ∃ c : ↥X, conjSub c ((secImg Ω (z * t) K).subgroupOf X) =
      (secImg Ω (z * t) J).subgroupOf X :=
    ⟨⟨k, hk⟩, by rw [conjSub_subgroupOf]; congr 1; rw [← ek, hg]⟩
  set x : ↥X := ⟨π ⟨z, hzY⟩, hKX hzb.mem⟩ with hxdef
  set x' : ↥X := ⟨π ⟨t, htY⟩, hJX htb.mem⟩ with hx'def
  have hx : IsUniqueInvolution ((secImg Ω (z * t) K).subgroupOf X) x :=
    isUniqueInvolution_subgroupOf hzb hKX
  have hx' : IsUniqueInvolution ((secImg Ω (z * t) J).subgroupOf X) x' :=
    isUniqueInvolution_subgroupOf htb hJX
  have hcenZ := hs.mk_mul_mk_mem_center hzY htY
  have hcen : x * x' ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcenZ (c : SecQuot Ω (z * t)))
  have hc1 : x * (x * x') = (x * x') * x := Subgroup.mem_center_iff.mp hcen x
  have hxx : x' * x = x * x' := by
    calc x' * x = x⁻¹ * ((x * x') * x) := by group
      _ = x⁻¹ * (x * (x * x')) := by rw [hc1]
      _ = x * x' := by group
  have hsq : x * x' * (x * x') = 1 := by
    calc x * x' * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hxx]
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hx.sq, hx'.sq, one_mul]
  set N : Subgroup ↥X := Subgroup.zpowers (x * x') with hNdef
  have hNle : N ≤ Subgroup.center ↥X := Subgroup.zpowers_le.mpr hcen
  have hNn : N.Normal := ⟨fun c hc d => by
    have hcd := Subgroup.mem_center_iff.mp (hNle hc) d
    rw [hcd, mul_assoc, mul_inv_cancel, mul_one]
    exact hc⟩
  have hN2 : IsPGroup 2 ↥N := Balance.isPGroup_zpowers_of_mul_self_eq_one hsq
  obtain ⟨S', hdat, hq, hsg, hof, hhyp, hae, htw', hne⟩ :=
    twinQuotDatum ↥X (restrictFamily Φ X) hΦX hOX hAX _ hA hgenA _ hB hAB x x' hx hx' hcen N rfl
  have hlt : Nat.card (↥X ⧸ N) < n := by
    have h1 : Nat.card (↥X ⧸ N) ≤ Nat.card ↥X :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective N)
    have h2 : Nat.card ↥X ≤ Nat.card (SecQuot Ω (z * t)) := Subgroup.card_le_card_group _
    omega
  have haY : z * t ∈ layerY Ω (z * t) := (layerY Ω (z * t)).mul_mem hzY htY
  have hxx' : ((x * x' : ↥X) : SecQuot Ω (z * t)) = π ⟨z * t, haY⟩ := by
    show π ⟨z, hzY⟩ * π ⟨t, htY⟩ = π ⟨z * t, haY⟩
    rw [← map_mul]
    rfl
  rcases twinSectSetType3 n hs.large.below htw (↥X ⧸ N) hlt _ S' _ hdat hq hsg hof hhyp hae
      ⟨_, htw', hne⟩ with h2 | h4' | ⟨hom, -⟩
  · exfalso
    apply hE2
    obtain ⟨P, hPn, hP2, hxP⟩ := h2
    refine ⟨P.comap (QuotientGroup.mk' N), hPn.comap _, ?_, ?_⟩
    · exact hP2.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact hN2)
    · intro c hcz
      obtain ⟨w, hw, hwc⟩ := hcz
      have hw' : (w : Y) ∈ Subgroup.zpowers z := Subgroup.mem_subgroupOf.mp hw
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw'
      have hwm : w = (⟨z, hzY⟩ : ↥(layerY Ω (z * t))) ^ m := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow, ← hm]
      have hcm : c = x ^ m := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow, ← hwc, hwm, map_zpow]
      show QuotientGroup.mk' N c ∈ P
      rw [hcm, map_zpow]
      exact P.zpow_mem hxP m
  · left
    exact twinE4_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      (by rw [QuotientGroup.ker_mk']; exact hN2) h4'
  · right
    refine ⟨N, hNn, hN2, hNle, fun c => ?_, hom⟩
    constructor
    · intro hc
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      refine ⟨(⟨z * t, haY⟩ : ↥(layerY Ω (z * t))) ^ m, ?_, ?_⟩
      · show (⟨z * t, haY⟩ : ↥(layerY Ω (z * t))) ^ m ∈
          (Subgroup.zpowers (z * t)).subgroupOf (layerY Ω (z * t))
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_zpow]
        exact Subgroup.zpow_mem_zpowers _ m
      · rw [map_zpow, Subgroup.coe_zpow, hxx']
    · rintro ⟨w, hw, hwc⟩
      have hw' : (w : Y) ∈ Subgroup.zpowers (z * t) := Subgroup.mem_subgroupOf.mp hw
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw'
      have hwm : w = (⟨z * t, haY⟩ : ↥(layerY Ω (z * t))) ^ m := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow, ← hm]
      have hcm : c = (x * x') ^ m := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow, hxx', ← hwc, hwm, map_zpow]
      rw [hcm]
      exact Subgroup.zpow_mem_zpowers _ m

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
