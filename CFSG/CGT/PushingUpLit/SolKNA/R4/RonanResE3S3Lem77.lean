module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseSec
public import CFSG.ClassicalInvolution.Q3.TL4E3S3Orb
public import CFSG.ClassicalInvolution.Q3.TL4Conn264B

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem secInO2_of_four_le (hr : 4 ≤ r) (h4 : Thm4RBelow r n) (hB : TightBelowR r n)
    (hNo : NoQ16E4) (hs : TightStd8R r n Rd Sd z J S R T W t) :
    SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z := by
  by_cases hc : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t)
  swap
  · exact hs.secInO2_of_normal (hs.secImg_normal_of_not_conj h4 hc).1
  obtain ⟨g, hg⟩ := hc
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ := h.secFam (x := z * t)
  have hO := secQuot_oddCore_eq_bot (Ω := Ω) (x := z * t)
  have hn := hs.natCard_secQuot_lt
  have hgen := omegaGen_secFam (Ω := Ω) (x := z * t)
  have hK := secImg_mem hs.xMem_K
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have hzb := isUniqueInvolution_secImg h hs.xMem_K hs.hz
  have hne := not_tightEdgeless_orbGrp h4 hΦ hO hn hK hs.secImg_J_mem_omegaNbr
    (by rw [hgen]; exact Subgroup.mem_top g) hg
  obtain ⟨S', hd, hcl⟩ := tightClsR_orbGrp (by omega) h4 hΦ hO hn hK hzb
  have hlt : Nat.card ↥(Vtx.orbGrp (TL4.secFam Ω (z * t)) (secImg Ω (z * t) (tightCore Rd))) < n :=
    lt_of_le_of_lt (Subgroup.card_le_card_group _) hn
  obtain ⟨P, hPn, hP2, hzP⟩ := inO2_of_edge_four_le hr hB hNo hlt hd hcl hne
  refine ⟨P, hPn, hP2, fun c hc => ?_⟩
  obtain ⟨w, hw, hwc⟩ := hc
  have hw' : (w : Y) ∈ Subgroup.zpowers z := Subgroup.mem_subgroupOf.mp hw
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw'
  have hwm : w = (⟨z, hzY⟩ : ↥(layerY Ω (z * t))) ^ m := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, ← hm]
  have e : c = (⟨QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨z, hzY⟩,
      Vtx.le_orbGrp _ hzb.mem⟩ : ↥(Vtx.orbGrp (TL4.secFam Ω (z * t)) (secImg Ω (z * t)
        (tightCore Rd)))) ^ m := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, ← map_zpow, ← hwm, hwc]
  rw [e]
  exact P.zpow_mem hzP m

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
