module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu9F
public import CFSG.ClassicalInvolution.Q3.TL4OddBadW
public import CFSG.ClassicalInvolution.Q3.TL4Conn26X
public import CFSG.ClassicalInvolution.Q3.Q3T7K00

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Fam

variable {X : Type} [Group X] {r : ℕ}

theorem TypeRFam.subfam {Φ Λ : Set (Subgroup X)} (h : TypeRFam r Φ) (hsub : Λ ⊆ Φ)
    (hinv : ConjInvariant Λ) : TypeRFam r Λ where
  hyp :=
    { conjInvariant := hinv
      omega1 := fun K hK => h.hyp.omega1 K (hsub hK)
      omega2 := fun K hK => h.hyp.omega2 K (hsub hK)
      omega3 := fun K hK J hJ => h.hyp.omega3 K (hsub hK) J (hsub hJ)
      omega4 := fun K hK J hJ => h.hyp.omega4 K (hsub hK) J (hsub hJ)
      omega5 := fun K hK J hJ => h.hyp.omega5 K (hsub hK) J (hsub hJ) }
  cls :=
    { subnormal := fun K hK => h.cls.subnormal K (hsub hK)
      commOdd := fun J hJ => h.cls.commOdd J (hsub hJ) }
  twoGroup := fun L hL => h.twoGroup L (hsub hL)
  quat := fun L hL => h.quat L (hsub hL)
  tight := fun L hL => h.tight L (hsub hL)
  noTwins := fun L hL L' hL' => h.noTwins L (hsub hL) L' ⟨hsub hL'.1, hL'.2⟩

theorem mem_USet_restrictFamily_of_sylow {Φ : Set (Subgroup X)} {H J T U : Subgroup X}
    (hJ : J ∈ Φ) (hJH : J ≤ H) (hT : IsSylow2In T J) (hUT : U ≤ T) (hcyc : IsCyclic ↥U)
    (hidx : U.relIndex T = 2) : U.subgroupOf H ∈ USet (restrictFamily Φ H) := by
  have hTH : T ≤ H := hT.1.trans hJH
  have hUH : U ≤ H := hUT.trans hTH
  have hrel : (U.subgroupOf H).relIndex (T.subgroupOf H) = 2 := by
    have h2 := Subgroup.relIndex_map_map_of_injective (U.subgroupOf H) (T.subgroupOf H)
      H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hUH, Subgroup.map_subgroupOf_eq_of_le hTH] at h2
    rw [← h2]
    exact hidx
  exact ⟨T.subgroupOf H, mem_RSet_restrict hJ hJH hT, Subgroup.subgroupOf_mono H hUT,
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hUH)).mpr hcyc, hrel⟩

end Fam

section Defs

variable {Y : Type} [Group Y]

noncomputable abbrev linkGrp (R : Subgroup Y) (t : Y) :
    Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) t) :=
  omegaGen (coreLinkFam R t)

theorem le_linkGrp {R : Subgroup Y} {t : Y} {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    secImg (CoreAssembly.conjClass (tightCore R)) t J ≤ linkGrp R t :=
  le_omegaGen ⟨J, hJ, rfl⟩

theorem omegaGen_linkRestrict {R : Subgroup Y} {t : Y} :
    omegaGen (restrictFamily (coreLinkFam R t) (linkGrp R t)) = ⊤ :=
  omegaGen_restrictFamily_eq_top _ _ rfl

theorem subgroupOf_mem_linkRestrict {R : Subgroup Y} {t : Y} {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    (secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t) ∈
      restrictFamily (coreLinkFam R t) (linkGrp R t) :=
  subgroupOf_mem_restrictFamily ⟨J, hJ, rfl⟩ (le_linkGrp hJ)

theorem subgroupOf_linkGrp_ne {R : Subgroup Y} {t : Y} {J K'' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK : K'' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : secImg (CoreAssembly.conjClass (tightCore R)) t K'' ≠
      secImg (CoreAssembly.conjClass (tightCore R)) t J) :
    (secImg (CoreAssembly.conjClass (tightCore R)) t K'').subgroupOf (linkGrp R t) ≠
      (secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t) := by
  intro e
  apply hne
  have h1 := Subgroup.subgroupOf_inj.mp e
  rwa [inf_of_le_left (le_linkGrp hK), inf_of_le_left (le_linkGrp hJ)] at h1

theorem eq_of_mul_inv_mem {B O : Subgroup Y} (hBO : B ⊓ O = ⊥) {x b : Y} (hx : x ∈ B)
    (hb : b ∈ B) (hxb : x * b⁻¹ ∈ O) : x = b := by
  have h1 : x * b⁻¹ ∈ B ⊓ O := ⟨B.mul_mem hx (B.inv_mem hb), hxb⟩
  rw [hBO, Subgroup.mem_bot] at h1
  calc x = x * b⁻¹ * b := by group
    _ = b := by rw [h1, one_mul]

end Defs

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem coreLinkFam_conjInvariant (hL : TightLargeHypR r n Y R S t) :
    ConjInvariant (coreLinkFam R t) := by
  rintro gb _ ⟨J, hJ, rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  exact ⟨conjSub (g : Y) J, conjSub_mem_omegaNbr_core hL hJ (layerY_le_centralizer g.2),
    (conjSub_secImg g J).symm⟩

theorem typeRFam_coreLinkFam (hL : TightLargeHypR r n Y R S t) :
    TypeRFam r (coreLinkFam R t) :=
  ((TightLargeHypR.typeRFam hL).secFam (x := t)).subfam (coreLinkFam_subset hL)
    (coreLinkFam_conjInvariant hL)

theorem oddCore_linkGrp_eq_bot (hL : TightLargeHypR r n Y R S t) :
    classicalInvolutionOddCore ↥(linkGrp R t) = ⊥ := by
  have : (linkGrp R t).Normal := omegaGen_normal (coreLinkFam_conjInvariant hL)
  exact CFSG.ComponentClassification.OddCore.subnormal_corefree secQuot_oddCore_eq_bot _
    (IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤))



theorem omegaStarNbr_secFam_of_link (hL : TightLargeHypR r n Y R S t) {J K'' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK : K'' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h : (secImg (CoreAssembly.conjClass (tightCore R)) t K'').subgroupOf (linkGrp R t) ∈
      omegaStarNbr (restrictFamily (coreLinkFam R t) (linkGrp R t))
        ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))) :
    secImg (CoreAssembly.conjClass (tightCore R)) t K'' ∈
      omegaStarNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J) := by
  obtain ⟨-, hne, U', hU', hUK, hUN⟩ := h
  obtain ⟨T, ⟨M, hM, P, rfl⟩, hUT, hcyc, hidx⟩ := map_mem_USet_restrict hU'
  refine ⟨secImg_mem (xMem_of_mem_omegaNbr_core hL hK), fun e => hne (by rw [e]),
    U'.map (linkGrp R t).subtype, ⟨_, ⟨M, coreLinkFam_subset hL hM, P, rfl⟩, hUT, hcyc, hidx⟩,
    ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hUK hy)
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_subgroupOf_iff (le_linkGrp hJ)).mpr (hUN hy)

theorem omegaNbr_secFam_of_link (hL : TightLargeHypR r n Y R S t) {J K'' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK : K'' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h : (secImg (CoreAssembly.conjClass (tightCore R)) t K'').subgroupOf (linkGrp R t) ∈
      omegaNbr (restrictFamily (coreLinkFam R t) (linkGrp R t))
        ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))) :
    secImg (CoreAssembly.conjClass (tightCore R)) t K'' ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J) := by
  obtain ⟨-, hne, T', hT', hTK, hTN⟩ := h
  obtain ⟨M, hM, -, hTM⟩ := exists_isSylow2In_of_mem_RSet_restrict hT'
  refine ⟨secImg_mem (xMem_of_mem_omegaNbr_core hL hK), fun e => hne (by rw [e]),
    T'.map (linkGrp R t).subtype, mem_RSet_of_isSylow2In (coreLinkFam_subset hL hM) hTM, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hTK hy)
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_subgroupOf_iff (le_linkGrp hJ)).mpr (hTN hy)

theorem omegaNbr_link_of_secFam (hL : TightLargeHypR r n Y R S t) {J K'' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK : K'' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h : secImg (CoreAssembly.conjClass (tightCore R)) t K'' ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J)) :
    (secImg (CoreAssembly.conjClass (tightCore R)) t K'').subgroupOf (linkGrp R t) ∈
      omegaNbr (restrictFamily (coreLinkFam R t) (linkGrp R t))
        ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) := by
  have hΦ := (TightLargeHypR.typeRFam hL).secFam (x := t)
  obtain ⟨-, hne, T, hT, hTK, hTN⟩ := h
  have hTs := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ.hyp
    (secImg_mem (xMem_of_mem_omegaNbr_core hL hK)) hT hTK
  refine ⟨subgroupOf_mem_linkRestrict hK, subgroupOf_linkGrp_ne hJ hK hne,
    T.subgroupOf (linkGrp R t),
    mem_RSet_restrict ⟨K'', hK, rfl⟩ (le_linkGrp hK) hTs, Subgroup.subgroupOf_mono _ hTK, ?_⟩
  intro y hy
  exact (mem_normalizer_subgroupOf_iff (le_linkGrp hJ)).mp (hTN (Subgroup.mem_subgroupOf.mp hy))

theorem omegaStarNbr_link_of_secFam (hL : TightLargeHypR r n Y R S t) {J K'' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK : K'' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h : secImg (CoreAssembly.conjClass (tightCore R)) t K'' ∈
      omegaStarNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J)) :
    (secImg (CoreAssembly.conjClass (tightCore R)) t K'').subgroupOf (linkGrp R t) ∈
      omegaStarNbr (restrictFamily (coreLinkFam R t) (linkGrp R t))
        ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) := by
  have hΦ := (TightLargeHypR.typeRFam hL).secFam (x := t)
  have hKx := secImg_mem (xMem_of_mem_omegaNbr_core hL hK)
  obtain ⟨-, hne, U, hU, hUK, hUN⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΦ.hyp hU
  obtain ⟨T, hT, hUT, hcyc, hidx⟩ := hU
  obtain ⟨M, hM, hTM⟩ := exists_isSylow2In_of_mem_RSet hT
  have hMK := Sec6Gen.eq_of_le_of_le hΦ.hyp hM hKx (Sec6Gen.isPGroup_of_mem_USet hΦ.hyp
    ⟨T, hT, hUT, hcyc, hidx⟩) h4 (hUT.trans hTM.1) hUK
  rw [hMK] at hTM
  refine ⟨subgroupOf_mem_linkRestrict hK, subgroupOf_linkGrp_ne hJ hK hne,
    U.subgroupOf (linkGrp R t),
    mem_USet_restrictFamily_of_sylow ⟨K'', hK, rfl⟩ (le_linkGrp hK) hTM hUT hcyc hidx,
    Subgroup.subgroupOf_mono _ hUK, ?_⟩
  intro y hy
  exact (mem_normalizer_subgroupOf_iff (le_linkGrp hJ)).mp (hUN (Subgroup.mem_subgroupOf.mp hy))

theorem exists_starFrameAt_of_secId (hN : SecIdStarNbrId3) (hL : TightLargeHypR 3 n Y R S t)
    (hcase : LinkS3S4 R t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) : ∃ (K'' : Subgroup Y) (w : Y), StarFrameAt R t J K'' u w := by
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hcl := hΩ.conjInvariant
  have ht := hd.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨L', hL', hst, hnot⟩ := hN _ _ ((typeRFam_coreLinkFam hL).restrict (linkGrp R t))
    (oddCore_linkGrp_eq_bot hL) omegaGen_linkRestrict hcase.1 hcase.2 _
    (subgroupOf_mem_linkRestrict hJ)
  obtain ⟨_, ⟨K'', hK'', rfl⟩, -, rfl⟩ := hL'
  have hst' := omegaStarNbr_secFam_of_link hL hJ hK'' hst
  have hnn : secImg (CoreAssembly.conjClass (tightCore R)) t K'' ∉
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J) :=
    fun h' => hnot (omegaNbr_link_of_secFam hL hJ hK'' h')
  have hJx := xMem_of_mem_omegaNbr_core hL hJ
  obtain ⟨ν, hν, hstY⟩ := exists_conj_omegaStarNbr_of_secImg h hJx
    (xMem_of_mem_omegaNbr_core hL hK'') hst'
  have hνi : ν⁻¹ ∈ classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t) :=
    (classicalInvolutionOddCore _).inv_mem hν
  have hνt : ((ν⁻¹ : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) ∈
      Subgroup.centralizer ({t} : Set Y) := layerY_le_centralizer (ν⁻¹).2
  set c : Y := ((ν⁻¹ : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) with hcdef
  have hK3 := conjSub_mem_omegaNbr_core hL hK'' hνt
  have hsec := secImg_conj_of_mem hνi K''
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK''.1
  set K3 : Subgroup Y := conjSub c K'' with hK3def
  set w3 : Y := c * w * c⁻¹ with hw3def
  have hw3 : IsUniqueInvolution K3 w3 := hw.conj c
  have hstar3 : K3 ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) J := by
    have h1 := omegaStarNbr_conj hcl hstY c
    have e : conjSub c (conjSub (ν : Y) J) = J := by
      rw [hcdef, Subgroup.coe_inv, conjSub_inv_conjSub]
    rwa [e] at h1
  refine ⟨_, _, ⟨hJ, hK3, hstar3, fun hKJ => ?_, hu, hw3, by rw [hsec]; exact hst', by
    rw [hsec]; exact hnn⟩⟩
  have hKK := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK₀ hK3.1 hK3
  have hJK := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 hK3.1 hKJ
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have ntu : t ≠ u := fun e => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (e ▸ hu))
  obtain ⟨P, hP, -, hPt, hPu⟩ :=
    exists_isSylow2In_member_le_centralizer hL hK3.1 hw3 hKK hJK ht hu ntu ctu
  have huw := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hu hKJ hw3
  have hne : u ≠ w3 := fun e =>
    hKJ.2.1 (noTwins_of_large hL J hJ.1 K3 ⟨hK3.1, u, hu, e ▸ hw3⟩)
  have hadj := secImg_mem_omegaNbr hJx (xMem_of_mem_omegaNbr_core hL hK3) hP hPt
    (hPu.trans (h.tight J hJ.1 u hu)) (secImg_ne h hJx (xMem_of_mem_omegaNbr_core hL hK3) hu hw3
      huw hne)
  rw [hsec] at hadj
  exact hnn hadj

theorem tightStar289OrbR_of (hO : SecIdStarOrbId3) : TightStar289OrbR 3 n := by
  intro Y _ _ R S t hL hc hA hcase J K'' u w hF
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have hJx := xMem_of_mem_omegaNbr_core hL hF.memJ
  have hKx := xMem_of_mem_omegaNbr_core hL hF.memK
  have htY := mem_layerY_of_isUniqueInvolution h (xMem_core hL) hd.isUniqueInvolution_core
  have huY := mem_layerY_of_isUniqueInvolution h hJx hF.invJ
  have hwY := mem_layerY_of_isUniqueInvolution h hKx hF.invK
  have hstL := omegaStarNbr_link_of_secFam hL hF.memJ hF.memK hF.secStar
  have hnnL := fun h' => hF.secNotNbr (omegaNbr_secFam_of_link hL hF.memJ hF.memK h')
  have ha := isUniqueInvolution_subgroupOf (isUniqueInvolution_secImg h hJx hF.invJ)
    (le_linkGrp (t := t) hF.memJ)
  have hb := isUniqueInvolution_subgroupOf (isUniqueInvolution_secImg h hKx hF.invK)
    (le_linkGrp (t := t) hF.memK)
  obtain ⟨gb, hga, hgb⟩ := hO _ _ ((typeRFam_coreLinkFam hL).restrict (linkGrp R t))
    (oddCore_linkGrp_eq_bot hL) omegaGen_linkRestrict hcase.1 hcase.2 _
    (subgroupOf_mem_linkRestrict hF.memJ) _ hstL hnnL _ _ ha hb
  have hga' := congrArg Subtype.val hga
  have hgb' := congrArg Subtype.val hgb
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hga' hgb'
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective
    (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
  have hq : ∀ x : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t),
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass
        (tightCore R)) t)) (g₀ * x * g₀⁻¹) =
        (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t) *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass
          (tightCore R)) t)) x * (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)⁻¹ := by
    intro x
    rw [map_mul, map_mul, map_inv]
    rw [show QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass
      (tightCore R)) t)) g₀ = (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t) from hg₀]
  obtain ⟨z₁, hz₁N, hz₁⟩ := (QuotientGroup.mk'_eq_mk' _).mp ((hq ⟨u, huY⟩).trans hga')
  obtain ⟨z₂, hz₂N, hz₂⟩ := (QuotientGroup.mk'_eq_mk' _).mp
    ((hq ⟨w, hwY⟩).trans (hgb'.trans (map_mul _ _ _).symm))
  have e₁ : (g₀ : Y) * u * (g₀ : Y)⁻¹ = w * (z₁ : Y)⁻¹ := by
    have := congrArg Subtype.val hz₁
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    group
  have e₂ : (g₀ : Y) * w * (g₀ : Y)⁻¹ = u * w * (z₂ : Y)⁻¹ := by
    have := congrArg Subtype.val hz₂
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    group
  have hm := mem_closure_three_left t u w
  have hzO : ∀ z ∈ classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t),
      ((z : Y)) ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) :=
    fun z hz => ⟨z, hz, rfl⟩
  have hz₁O := (oddCoreOf _).inv_mem (hzO z₁ hz₁N)
  have hz₂O := (oddCoreOf _).inv_mem (hzO z₂ hz₂N)
  have hBLy : Subgroup.closure ({t, u, w} : Set Y) ≤
      layerY (CoreAssembly.conjClass (tightCore R)) t := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h1 | h1 | h1 <;> rw [h1] <;> assumption
  have hBN : Subgroup.closure ({t, u, w} : Set Y) ≤ Subgroup.normalizer
      ((oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) : Subgroup Y) : Set Y) :=
    fun b hb => mem_normalizer_oddCoreOf (hBLy hb)
  have hB2 : IsPGroup 2 ↥(Subgroup.closure ({t, u, w} : Set Y)) :=
    IsPGroup.of_card (n := 3) (by rw [hF.natCard hL]; norm_num)
  have hBO := S1916.inf_oddCoreOf_eq_bot hB2 (layerY (CoreAssembly.conjClass (tightCore R)) t)
  have hg₀t : (g₀ : Y) ∈ Subgroup.centralizer ({t} : Set Y) := layerY_le_centralizer g₀.2
  have hle : conjSub (g₀ : Y) (Subgroup.closure ({t, u, w} : Set Y)) ≤
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ⊔
        Subgroup.closure ({t, u, w} : Set Y) := by
    rw [conjSub, map_conj_closure_three, Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h1 | h1 | h1 <;> rw [h1]
    · rw [Subgroup.mem_centralizer_singleton_iff.mp hg₀t, mul_inv_cancel_right]
      exact Subgroup.mem_sup_right hm.1
    · rw [e₁]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hm.2.2) (Subgroup.mem_sup_left hz₁O)
    · rw [e₂]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hm.2.1)
        (Subgroup.mem_sup_right hm.2.2)) (Subgroup.mem_sup_left hz₂O)
  have hcard : Nat.card ↥(conjSub (g₀ : Y) (Subgroup.closure ({t, u, w} : Set Y))) =
      Nat.card ↥(Subgroup.closure ({t, u, w} : Set Y)) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.closure ({t, u, w} : Set Y))
      (MulAut.conj (g₀ : Y)).toMonoidHom (MulAut.conj (g₀ : Y)).injective).toEquiv).symm
  obtain ⟨ν, hνO, hνB⟩ := Q3T7M.CentQ.exists_conjSub_of_le_sup_odd hBN
    (oddCoreOf_odd_natCard _) hBO hB2 (isPGroup_conjSub _ hB2) hcard hle
  have hνLy : ν ∈ layerY (CoreAssembly.conjClass (tightCore R)) t :=
    Subgroup.map_subtype_le _ hνO
  set g : Y := ν⁻¹ * (g₀ : Y) with hgdef
  have hgN : g ∈ Subgroup.normalizer
      ((Subgroup.closure ({t, u, w} : Set Y) : Subgroup Y) : Set Y) := by
    rw [mem_normalizer_iff_conjSub_eq, hgdef, conjSub_mul, ← hνB, conjSub_inv_conjSub]
  have hgC : g ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (layerY_le_centralizer hνLy)) hg₀t
  have hconjB : ∀ b ∈ Subgroup.closure ({t, u, w} : Set Y),
      g * b * g⁻¹ ∈ Subgroup.closure ({t, u, w} : Set Y) := by
    intro b hb
    have h1 := conj_mem_conjSub hb g
    rwa [mem_normalizer_iff_conjSub_eq.mp hgN] at h1
  have hnO : ∀ x ∈ layerY (CoreAssembly.conjClass (tightCore R)) t,
      ∀ o ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t),
        x * o * x⁻¹ ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) :=
    fun x hx o ho => (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCoreOf hx) o).mp ho
  have hgu : g * u * g⁻¹ = w := by
    refine eq_of_mul_inv_mem hBO (hconjB u hm.2.1) hm.2.2 ?_
    have e : g * u * g⁻¹ * w⁻¹ = ν⁻¹ * (w * ((z₁ : Y)⁻¹ * ν) * w⁻¹) := by
      calc g * u * g⁻¹ * w⁻¹ = ν⁻¹ * ((g₀ : Y) * u * (g₀ : Y)⁻¹) * ν * w⁻¹ := by
            rw [hgdef]; group
        _ = ν⁻¹ * (w * ((z₁ : Y)⁻¹ * ν) * w⁻¹) := by rw [e₁]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hνO)
      (hnO w hwY _ (Subgroup.mul_mem _ hz₁O hνO))
  have hgw : g * w * g⁻¹ = u * w := by
    refine eq_of_mul_inv_mem hBO (hconjB w hm.2.2) (Subgroup.mul_mem _ hm.2.1 hm.2.2) ?_
    have e : g * w * g⁻¹ * (u * w)⁻¹ =
        ν⁻¹ * ((u * w) * ((z₂ : Y)⁻¹ * ν) * (u * w)⁻¹) := by
      calc g * w * g⁻¹ * (u * w)⁻¹ = ν⁻¹ * ((g₀ : Y) * w * (g₀ : Y)⁻¹) * ν * (u * w)⁻¹ := by
            rw [hgdef]; group
        _ = ν⁻¹ * ((u * w) * ((z₂ : Y)⁻¹ * ν) * (u * w)⁻¹) := by rw [e₂]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hνO)
      (hnO (u * w) (Subgroup.mul_mem _ huY hwY) _ (Subgroup.mul_mem _ hz₂O hνO))
  exact ⟨g, hgN, by rw [Subgroup.mem_centralizer_singleton_iff.mp hgC, mul_inv_cancel_right],
    hgu, hgw⟩

theorem alphaOf_eq_bot_of_star289_secId (hN : SecIdStarNbrId3) (hO : SecIdStarOrbId3)
    (hz : TightStar289ZR 3 n) (ht : TightStar289TR 3 n) (hzt : TightStar289ZTR 3 n)
    (hg : TightStar289GenR 3 n) (hL : TightLargeHypR 3 n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hA : ¬ TriNbrAll R t)
    (hcase : LinkS3S4 R t) :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ :=
  alphaOf_eq_bot_of_star289 hz ht hzt (tightStar289OrbR_of hO) hg hL hc hA hcase
    (fun _ hJ _ hu => exists_starFrameAt_of_secId hN hL hcase hJ hu)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
