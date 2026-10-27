module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y}

private theorem normalizer_secImg_core_eq_topR (hL : TightLargeHypR r n Y R S t) :
    Subgroup.normalizer (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) :
      Set (SecQuot (CoreAssembly.conjClass (tightCore R)) t)) = ⊤ := by
  have h := TightLargeHypR.typeRFam hL
  have hΦ := h.secFam (x := t)
  have hK := secImg_mem (xMem_core hL)
  have hu := isUniqueInvolution_secImg h (xMem_core hL) hL.datum.isUniqueInvolution_core
  refine eq_top_iff.mpr (le_trans (fun g _ => ?_) (hΦ.tight _ hK _ hu))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (layerY_le_centralizer g.2))

private theorem commutes_secImg_core_of_isSylow2InR (hL : TightLargeHypR r n Y R S t)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {V : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) t)}
    (hV : IsSylow2In V (secImg (CoreAssembly.conjClass (tightCore R)) t J)) :
    Commutes (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R)) V := by
  have h := TightLargeHypR.typeRFam hL
  have hΦ := h.secFam (x := t)
  have hK := secImg_mem (xMem_core hL)
  have hJΦ := secImg_mem (xMem_of_mem_omegaNbr_core hL hJ)
  have hK2 := isPGroup_secImg_core hL
  have hu := isUniqueInvolution_secImg h (xMem_core hL) hL.datum.isUniqueInvolution_core
  have hVR := mem_RSet_of_isSylow2In hJΦ hV
  have hVN : V ≤ Subgroup.normalizer
      (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) : Set _) := by
    rw [normalizer_secImg_core_eq_topR hL]
    exact le_top
  obtain ⟨P, hPS⟩ := (hV.2.1.to_sup_of_normal_right' hK2 hVN).exists_le_sylow
  have hne : secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) ≠ V := by
    intro e
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hJΦ
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΦ.hyp hVR
    have hzV : z ∈ V := T3.mem_of_isPGroup hz hV.1 hV.2.1 (by omega)
    rw [← e] at hzV
    have hzu := (hu.unique z hzV hz.sq).resolve_left hz.ne_one
    rw [hzu] at hz
    exact (secImg_mem_omegaNbr_secImg_core hL hJ).2.1 (hΦ.noTwins _ hK _ ⟨hJΦ, _, hu, hz⟩)
  exact Q3CP.l67Gen _ (TL4.secFam (CoreAssembly.conjClass (tightCore R)) t) hΦ.hyp P _
    (TC.mem_RSet_of_isPGroup hK hK2) V hVR (le_sup_right.trans hPS) (le_sup_left.trans hPS) hne

private theorem secImg_le_centralizer_secImg_coreR (hL : TightLargeHypR r n Y R S t)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    secImg (CoreAssembly.conjClass (tightCore R)) t J ≤ Subgroup.centralizer
      (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) : Set _) := by
  have hJX := xMem_of_mem_omegaNbr_core hL hJ
  have hle : coreAt t J ≤ ((Subgroup.centralizer
      (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) : Set _)).comap
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)))).map
            (layerY (CoreAssembly.conjClass (tightCore R)) t).subtype := by
    rw [← closure_twoElts_coreAt, Subgroup.closure_le]
    rintro g ⟨hgc, hg2⟩
    have hgY := coreAt_le_layerY hJX hgc
    refine ⟨⟨g, hgY⟩, ?_, rfl⟩
    have hmem : QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨g, hgY⟩ ∈
          secImg (CoreAssembly.conjClass (tightCore R)) t J :=
      ⟨⟨g, hgY⟩, Subgroup.mem_subgroupOf.mpr hgc, rfl⟩
    have h2 := ((isPGroup_zpowers_coe_iff (v := ⟨g, hgY⟩)).mp hg2).map
      (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)))
    rw [MonoidHom.map_zpowers] at h2
    obtain ⟨V, hV, hgV⟩ := IsSylow2In.exists_ge h2 (Subgroup.zpowers_le.mpr hmem)
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro k hk
    exact commutes_secImg_core_of_isSylow2InR hL hJ hV k hk _ (hgV (Subgroup.mem_zpowers _))
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨w', hw', e⟩ := hle (Subgroup.mem_subgroupOf.mp hw)
  obtain rfl : w' = w := Subtype.ext e
  exact hw'

private theorem linkGrp_le_centralizerR (hL : TightLargeHypR r n Y R S t) :
    linkGrp R t ≤ Subgroup.centralizer
      (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) : Set _) := by
  refine iSup₂_le fun Lb hLb => ?_
  obtain ⟨J, hJ, rfl⟩ := hLb
  exact secImg_le_centralizer_secImg_coreR hL hJ

theorem commutator_mem_oddCoreOf_linkLayerR (hL : TightLargeHypR r n Y R S t) {x : Y}
    (hx : x ∈ coreAt t (tightCore R)) {y : Y} (hy : y ∈ linkLayer R t) :
    x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t) := by
  have hxC := coreAt_le_centralizer t (tightCore R) hx
  have hxy : x * y * x⁻¹ ∈ linkLayer R t := conj_mem_linkLayer hL hxC hy
  have hc : x * y * x⁻¹ * y⁻¹ ∈ linkLayer R t := (linkLayer R t).mul_mem hxy
    ((linkLayer R t).inv_mem hy)
  suffices hk : (⟨_, hc⟩ : ↥(linkLayer R t)) ∈ (linkLayerHom' hL).ker by
    rw [ker_linkLayerHom hL] at hk
    exact ⟨⟨_, hc⟩, hk, rfl⟩
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  show linkLayerHom hL ⟨_, hc⟩ = 1
  have hxL := coreAt_le_layerY (xMem_core hL) hx
  have hyL := linkLayer_le_layerY hL hy
  have hxK : QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨x, hxL⟩ ∈
        secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) :=
    ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hyX : QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨y, hyL⟩ ∈ linkGrp R t := by
    have := linkLayerHom_mem hL ⟨y, hy⟩
    rwa [linkLayerHom_apply] at this
  have hcomm := Subgroup.mem_centralizer_iff.mp (linkGrp_le_centralizerR hL hyX) _ hxK
  rw [linkLayerHom_apply]
  have e : (⟨x * y * x⁻¹ * y⁻¹, linkLayer_le_layerY hL hc⟩ :
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) =
      ⟨x, hxL⟩ * ⟨y, hyL⟩ * ⟨x, hxL⟩⁻¹ * ⟨y, hyL⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

theorem linkLayer_commutator_mem_oddCoreOf_coreR (hL : TightLargeHypR r n Y R S t) {y : Y}
    (hy : y ∈ linkLayer R t) {x : Y} (hx : x ∈ tightCore R) :
    y * x * y⁻¹ * x⁻¹ ∈ oddCoreOf (tightCore R) := by
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hNt : Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) :=
    (TightLargeHypR.typeRFam hL).tight _ hK t ht
  let H : Subgroup Y :=
    { carrier := {y | conjSub y (tightCore R) = tightCore R ∧
        ∀ x ∈ tightCore R, y * x * y⁻¹ * x⁻¹ ∈ oddCoreOf (tightCore R)}
      one_mem' := ⟨conjSub_one _, fun x _ => by
        rw [show (1 : Y) * x * 1⁻¹ * x⁻¹ = 1 by group]
        exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨by rw [conjSub_mul, hb, ha], fun x hx => ?_⟩
        have h3 := Subgroup.mul_mem _ (conj_mem_oddCoreOf ha (hb' x hx)) (ha' x hx)
        rwa [show a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) =
          a * b * x * (a * b)⁻¹ * x⁻¹ by group] at h3
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        have ha1 : conjSub a⁻¹ (tightCore R) = tightCore R := by
          conv_lhs => rw [← ha]
          rw [conjSub_inv_conjSub]
        refine ⟨ha1, fun x hx => ?_⟩
        have h2 := Subgroup.inv_mem _ (ha' _ (conj_mem_of_conjSub_eq ha1 hx))
        rwa [show (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * x * a⁻¹⁻¹)⁻¹)⁻¹ =
          a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ by group] at h2 }
  suffices hle : linkLayer R t ≤ H from (hle hy).2 x hx
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨u', hu'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨hJΩ, hJne, T, hT, hTJ, hTN⟩ := id hJ
  have hTs : IsSylow2In T J := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hT hJΩ hTJ
  have hTt : T ≤ Subgroup.centralizer ({t} : Set Y) := fun z hz =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hTN hz)
  have hTs' : IsSylow2In T (J ⊓ Subgroup.centralizer ({t} : Set Y)) :=
    ⟨le_inf hTJ hTt, hTs.2.1, fun V' hV'M hV'2 hle => hTs.2.2 V' (hV'M.trans inf_le_left) hV'2 hle⟩
  show tightCore (J ⊓ Subgroup.centralizer ({t} : Set Y)) ≤ H
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨hgJt, hg2⟩
  obtain ⟨V, hV, hgV⟩ := IsSylow2In.exists_ge hg2 (Subgroup.zpowers_le.mpr hgJt)
  obtain ⟨c, hc, hcV⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hTs' hV
  have hVJ : IsSylow2In V J := by
    rw [← hcV]
    have h1 := hTs.conj c
    rwa [conjSub_eq_self_of_mem hc.1] at h1
  have hcomm := Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ hK hJΩ
    (Ne.symm hJne) ht hu' hVJ (hV.1.trans inf_le_right)
  refine ⟨mem_normalizer_iff_conjSub_eq.mp (hNt hgJt.2), fun x hx => ?_⟩
  exact hcomm (Subgroup.commutator_mem_commutator (hgV (Subgroup.mem_zpowers g)) hx)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
