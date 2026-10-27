module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

namespace E3S3O

section Cit3

theorem stepC_proved {n : ℕ} : StepC n := by
  intro Y _ _ R S t J u L Rd Sd S' R' T W h s hs hsa hW
  have hΦ := (TightLargeHypR.typeRFam h.std.large).secFam (x := u * t)
  have hcl := hΦ.hyp.conjInvariant
  have hJb := secImg_mem h.std.xMem_K
  have hD : imgD Rd L (u * t) ≤ orbW Rd (u * t) := by
    refine iSup₂_le fun M hM => ?_
    obtain ⟨c, hc, e⟩ := h.exists_conj_of_nbr hs hM.1 hM.2
    rw [← e]
    exact Vtx.conjSub_le_orbGrp _ ⟨c, Vtx.orbGrp_le hcl hJb hc⟩
  refine ⟨hD, le_antisymm (iSup₂_le fun M hM => ?_) fun x hx => ?_⟩
  · obtain ⟨⟨c, hc⟩, hfix⟩ := hM
    have hc' : conjSub c (imgW Rd (u * t) (tightCore Rd)) = M := hc
    subst hc'
    obtain ⟨Mb, hMb⟩ : ∃ Mb, Mb = conjSub c.1
        (secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore Rd)) := ⟨_, rfl⟩
    have e1 : conjSub c (imgW Rd (u * t) (tightCore Rd)) = Mb.subgroupOf (orbW Rd (u * t)) := by
      rw [hMb]
      exact conjSub_subgroupOf _ c _
    have hMbW : Mb ≤ orbW Rd (u * t) := by
      rw [hMb]
      exact Vtx.conjSub_le_orbGrp _ ⟨c.1, Vtx.orbGrp_le hcl hJb c.2⟩
    have hMbΦ : Mb ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (u * t) := by
      rw [hMb]
      exact hcl _ _ hJb
    obtain ⟨M₀, hM₀, hM₀a, hM₀b⟩ := h.exists_nbr_of_fixed hs hMbΦ fun m hm =>
      congrArg Subtype.val (hfix ⟨m, hMbW hm⟩ (by rw [e1]; exact Subgroup.mem_subgroupOf.mpr hm))
    intro x hx
    rw [e1] at hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hle : secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) M₀ ≤ imgD Rd L (u * t) :=
      le_iSup₂ (f := fun M (_ : M ∈ {M | M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L ∧
        XMem (CoreAssembly.conjClass (tightCore Rd)) (u * t) M}) =>
          secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) M) M₀ ⟨hM₀, hM₀a⟩
    exact hle (hM₀b ▸ Subgroup.mem_subgroupOf.mp hx)
  · have key : imgD Rd L (u * t) ≤ (sigmaFixGen (imgW Rd (u * t) (tightCore Rd))
        (sig Rd hsa hW)).map (orbW Rd (u * t)).subtype := by
      refine iSup₂_le fun M hM => ?_
      obtain ⟨c, hc, e⟩ := h.exists_conj_of_nbr hs hM.1 hM.2
      have hfixM := secAct_eq_of_le_centralizer (conjInvariant_conjClass (tightCore Rd)) hsa
        (h.le_centralizer_of_mem' hs hM.1)
      have hle : conjSub (⟨c, hc⟩ : ↥(orbW Rd (u * t))) (imgW Rd (u * t) (tightCore Rd)) ≤
          sigmaFixGen (imgW Rd (u * t) (tightCore Rd)) (sig Rd hsa hW) := by
        refine le_iSup₂ (f := fun M (_ : M ∈ {M | M ∈ CoreAssembly.conjClass
          (imgW Rd (u * t) (tightCore Rd)) ∧ ∀ x ∈ M, sig Rd hsa hW x = x}) => M) _
          ⟨⟨⟨c, hc⟩, rfl⟩, fun y hy => Subtype.ext ?_⟩
        rw [conjSub_subgroupOf, Subgroup.mem_subgroupOf, e] at hy
        exact hfixM _ hy
      intro m hm
      have hmW : m ∈ orbW Rd (u * t) :=
        e ▸ Vtx.conjSub_le_orbGrp _ ⟨c, Vtx.orbGrp_le hcl hJb hc⟩ <| hm
      refine ⟨⟨m, hmW⟩, hle ?_, rfl⟩
      rw [conjSub_subgroupOf, Subgroup.mem_subgroupOf, e]
      exact hm
    obtain ⟨y, hy, hyx⟩ := key (Subgroup.mem_subgroupOf.mp hx)
    rwa [show y = x from Subtype.ext hyx] at hy

theorem stepD_proved {n : ℕ} : StepD n := by
  intro Y _ _ R S t J u L Rd Sd S' R' T W h s hs hsa hW M hM hfix hnbr
  have hΦ := (TightLargeHypR.typeRFam h.std.large).secFam (x := u * t)
  have hcl := hΦ.hyp.conjInvariant
  have hJb := secImg_mem h.std.xMem_K
  have hJbW : secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore Rd) ≤
      orbW Rd (u * t) := Vtx.le_orbGrp _
  obtain ⟨c, hc⟩ := hM
  have hc' : conjSub c (imgW Rd (u * t) (tightCore Rd)) = M := hc
  subst hc'
  obtain ⟨hMfam, hne, P, hP, hPM, hPN⟩ := hnbr
  obtain ⟨Mb, hMb⟩ : ∃ Mb, Mb = conjSub c.1
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore Rd)) := ⟨_, rfl⟩
  have e1 : conjSub c (imgW Rd (u * t) (tightCore Rd)) = Mb.subgroupOf (orbW Rd (u * t)) := by
    rw [hMb]
    exact conjSub_subgroupOf _ c _
  have hMbW : Mb ≤ orbW Rd (u * t) := by
    rw [hMb]
    exact Vtx.conjSub_le_orbGrp _ ⟨c.1, Vtx.orbGrp_le hcl hJb c.2⟩
  have hMbΦ : Mb ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (u * t) := by
    rw [hMb]
    exact hcl _ _ hJb
  obtain ⟨M₀, hM₀, hM₀a, hM₀b⟩ := h.exists_nbr_of_fixed hs hMbΦ fun m hm =>
    congrArg Subtype.val (hfix ⟨m, hMbW hm⟩ (by rw [e1]; exact Subgroup.mem_subgroupOf.mpr hm))
  have hPs := Sec6Gen.isSylow2In_of_mem_RSet_of_le (hΦ.restrict (orbW Rd (u * t))).hyp hMfam hP hPM
  rw [e1] at hPs
  have hPs' := isSylow2In_map_subtype_iff.mpr hPs
  rw [Subgroup.map_subgroupOf_eq_of_le hMbW, ← hM₀b] at hPs'
  obtain ⟨T₀, hT₀, hT₀P⟩ := exists_sylow_coreAt_of_isSylow2In hM₀a hPs'
  have key := h.secImg_eq_of_normalizes hs hM₀ hM₀a hT₀ fun τ hτ => by
    have hmem : QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t)))
          ⟨τ, coreAt_le_layerY hM₀a (hT₀.1 hτ)⟩ ∈ P.map (orbW Rd (u * t)).subtype := by
      rw [← hT₀P]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr hτ, rfl⟩
    obtain ⟨p, hp, hpτ⟩ := hmem
    rw [← hpτ]
    exact (mem_normalizer_subgroupOf_iff hJbW).mpr (hPN hp)
  apply hne
  rw [e1, ← hM₀b, key]

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
