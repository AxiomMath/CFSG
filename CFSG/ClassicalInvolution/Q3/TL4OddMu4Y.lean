module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu9L
public import CFSG.ClassicalInvolution.AschTight.S1916Help

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Comm

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem commutes_of_mem_omegaNbr_of_isPGroup (hΦ : HypOmegaGen Φ) {A B : Subgroup X}
    (hA : A ∈ Φ) (hA2 : IsPGroup 2 ↥A) (hB2 : IsPGroup 2 ↥B) (hB : B ∈ omegaNbr Φ A) :
    Commutes A B := by
  obtain ⟨hBΦ, hne, T, hT, hTB, hTN⟩ := hB
  have hTs : IsSylow2In T B := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΦ hT hBΦ hTB
  have hTB' : T = B := (hTs.2.2 B le_rfl hB2 hTB).symm
  have hBN : B ≤ Subgroup.normalizer (A : Set X) := hTB' ▸ hTN
  have hP : IsPGroup 2 ↥(B ⊔ A : Subgroup X) := hB2.to_sup_of_normal_right' hA2 hBN
  obtain ⟨P, hPS⟩ := hP.exists_le_sylow
  exact Q3CP.l67Gen X Φ hΦ P A (TC.mem_RSet_of_isPGroup hA hA2) B
    (TC.mem_RSet_of_isPGroup hBΦ hB2) (le_sup_right.trans hPS) (le_sup_left.trans hPS)
    (Ne.symm hne)

theorem isPGroup_of_quot_oddCore_eq_bot {H : Type} [Group H]
    (h2 : IsPGroup 2 (H ⧸ classicalInvolutionOddCore H))
    (hO : classicalInvolutionOddCore H = ⊥) : IsPGroup 2 H := by
  intro h
  obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk h)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hO, Subgroup.mem_bot] at hk
  exact hk

end Comm

section Defs

variable {Y : Type} [Group Y]

@[expose] noncomputable def linkLayerAt (Ω : Set (Subgroup Y)) (M : Subgroup Y) (a : Y) :
    Subgroup Y :=
  ⨆ J ∈ omegaNbr Ω M, coreAt a J

noncomputable abbrev linkLayer (R : Subgroup Y) (t : Y) : Subgroup Y :=
  linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t

variable {Ω : Set (Subgroup Y)} {M : Subgroup Y} {a : Y}

theorem coreAt_le_linkLayerAt {J : Subgroup Y} (hJ : J ∈ omegaNbr Ω M) :
    coreAt a J ≤ linkLayerAt Ω M a :=
  le_iSup₂_of_le J hJ le_rfl

theorem linkLayerAt_le_centralizer : linkLayerAt Ω M a ≤ Subgroup.centralizer ({a} : Set Y) :=
  iSup₂_le fun J _ => coreAt_le_centralizer a J

theorem conjSub_coreAt_conj (g : Y) (L : Subgroup Y) :
    conjSub g (coreAt a L) = coreAt (g * a * g⁻¹) (conjSub g L) := by
  unfold coreAt
  rw [conjSub_tightCore]
  congr 1
  show (L ⊓ Subgroup.centralizer ({a} : Set Y)).map (MulAut.conj g).toMonoidHom = _
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]
  show conjSub g L ⊓ conjSub g (Subgroup.centralizer ({a} : Set Y)) = _
  rw [Balance.conjSub_centralizer_singleton]

theorem conjSub_linkLayerAt (hΩ : ConjInvariant Ω) (g : Y) :
    conjSub g (linkLayerAt Ω M a) = linkLayerAt Ω (conjSub g M) (g * a * g⁻¹) := by
  apply le_antisymm
  · have hle : linkLayerAt Ω M a ≤
        conjSub g⁻¹ (linkLayerAt Ω (conjSub g M) (g * a * g⁻¹)) := by
      refine iSup₂_le fun J hJ => ?_
      have h1 : conjSub g (coreAt a J) ≤ linkLayerAt Ω (conjSub g M) (g * a * g⁻¹) := by
        rw [conjSub_coreAt_conj]
        exact coreAt_le_linkLayerAt (omegaNbr_conj hΩ hJ g)
      have h2 := conjSub_mono (n := g⁻¹) h1
      rwa [conjSub_inv_conjSub] at h2
    have h3 := conjSub_mono (n := g) hle
    rwa [conjSub_conjSub_inv] at h3
  · refine iSup₂_le fun J' hJ' => ?_
    have hJ : conjSub g⁻¹ J' ∈ omegaNbr Ω M := by
      have h1 := omegaNbr_conj hΩ hJ' g⁻¹
      rwa [conjSub_inv_conjSub] at h1
    have e : J' = conjSub g (conjSub g⁻¹ J') := (conjSub_conjSub_inv g J').symm
    rw [e, ← conjSub_coreAt_conj]
    exact conjSub_mono (coreAt_le_linkLayerAt hJ)

theorem conj_mem_linkLayerAt (hΩ : ConjInvariant Ω) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({a} : Set Y)) (hcM : conjSub c M = M) {y : Y}
    (hy : y ∈ linkLayerAt Ω M a) : c * y * c⁻¹ ∈ linkLayerAt Ω M a := by
  have h1 := conj_mem_conjSub hy c
  rw [conjSub_linkLayerAt hΩ, hcM, Subgroup.mem_centralizer_singleton_iff.mp hc,
    mul_inv_cancel_right] at h1
  exact h1

end Defs

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem conj_mem_linkLayer (hL : TightLargeHypR r n Y R S t) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) {y : Y} (hy : y ∈ linkLayer R t) :
    c * y * c⁻¹ ∈ linkLayer R t := by
  have hci : c⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) :=
    (Subgroup.centralizer ({t} : Set Y)).inv_mem hc
  have hle : linkLayer R t ≤ conjSub c⁻¹ (linkLayer R t) := by
    refine iSup₂_le fun J hJ => ?_
    have h1 : conjSub c (coreAt t J) ≤ linkLayer R t := by
      rw [conjSub_coreAt t hc]
      exact coreAt_le_linkLayerAt (conjSub_mem_omegaNbr_core hL hJ hc)
    have h2 := conjSub_mono (n := c⁻¹) h1
    rwa [conjSub_inv_conjSub] at h2
  have h3 := hle hy
  rwa [mem_conjSub_iff, inv_inv] at h3

theorem linkLayer_le_layerY (hL : TightLargeHypR r n Y R S t) :
    linkLayer R t ≤ layerY (CoreAssembly.conjClass (tightCore R)) t :=
  iSup₂_le fun _ hJ => coreAt_le_layerY (xMem_of_mem_omegaNbr_core hL hJ)

@[expose] noncomputable def linkLayerHom (hL : TightLargeHypR r n Y R S t) :
    ↥(linkLayer R t) →* SecQuot (CoreAssembly.conjClass (tightCore R)) t :=
  (QuotientGroup.mk' (classicalInvolutionOddCore
    ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))).comp
      (Subgroup.inclusion (linkLayer_le_layerY hL))

theorem linkLayerHom_apply (hL : TightLargeHypR r n Y R S t) (y : ↥(linkLayer R t)) :
    linkLayerHom hL y = QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨y, linkLayer_le_layerY hL y.2⟩ :=
  rfl

theorem range_linkLayerHom (hL : TightLargeHypR r n Y R S t) :
    (linkLayerHom hL).range = linkGrp R t := by
  apply le_antisymm
  · have hle : linkLayer R t ≤ ((linkGrp R t).comap (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)))).map
          (layerY (CoreAssembly.conjClass (tightCore R)) t).subtype := by
      refine iSup₂_le fun _ hJ => ?_
      intro c hc
      have hcY := coreAt_le_layerY (xMem_of_mem_omegaNbr_core hL hJ) hc
      exact ⟨⟨c, hcY⟩, le_linkGrp hJ ⟨⟨c, hcY⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩, rfl⟩
    rintro _ ⟨y, rfl⟩
    obtain ⟨c, hc, hcy⟩ := hle y.2
    rw [linkLayerHom_apply]
    have e : (⟨y, linkLayer_le_layerY hL y.2⟩ :
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) = c := Subtype.ext hcy.symm
    rw [e]
    exact hc
  · refine iSup₂_le fun Lb hLb => ?_
    obtain ⟨J, hJ, rfl⟩ := hLb
    rintro _ ⟨c, hc, rfl⟩
    have hcJ : (c : Y) ∈ coreAt t J := Subgroup.mem_subgroupOf.mp hc
    exact ⟨⟨c, coreAt_le_linkLayerAt hJ hcJ⟩, rfl⟩

theorem linkLayerHom_mem (hL : TightLargeHypR r n Y R S t) (y : ↥(linkLayer R t)) :
    linkLayerHom hL y ∈ linkGrp R t := by
  rw [← range_linkLayerHom hL]
  exact ⟨y, rfl⟩

@[expose] noncomputable def linkLayerHom' (hL : TightLargeHypR r n Y R S t) :
    ↥(linkLayer R t) →* ↥(linkGrp R t) :=
  (linkLayerHom hL).codRestrict (linkGrp R t) (linkLayerHom_mem hL)

theorem linkLayerHom'_surjective (hL : TightLargeHypR r n Y R S t) :
    Function.Surjective (linkLayerHom' hL) := by
  rintro ⟨g, hg⟩
  rw [← range_linkLayerHom hL] at hg
  obtain ⟨y, rfl⟩ := hg
  exact ⟨y, rfl⟩

theorem ker_linkLayerHom (hL : TightLargeHypR r n Y R S t) :
    (linkLayerHom' hL).ker = classicalInvolutionOddCore ↥(linkLayer R t) := by
  apply le_antisymm
  · have hmap : (linkLayerHom' hL).ker.map (Subgroup.inclusion (linkLayer_le_layerY hL)) ≤
        classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t) := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : linkLayerHom hL y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      rw [linkLayerHom_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hodd : Odd (Nat.card (linkLayerHom' hL).ker) := by
      have h1 := Subgroup.card_dvd_of_le hmap
      rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)] at h1
      exact odd_natCard_oddCore_layerY.of_dvd_nat h1
    exact le_sSup ⟨inferInstance, hodd⟩
  · intro y hy
    have hN : ((classicalInvolutionOddCore ↥(linkLayer R t)).map (linkLayerHom' hL)).Normal :=
      Subgroup.Normal.map inferInstance _ (linkLayerHom'_surjective hL)
    have hodd : Odd (Nat.card ((classicalInvolutionOddCore ↥(linkLayer R t)).map
        (linkLayerHom' hL))) :=
      (CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hle : (classicalInvolutionOddCore ↥(linkLayer R t)).map (linkLayerHom' hL) ≤
        classicalInvolutionOddCore ↥(linkGrp R t) := le_sSup ⟨hN, hodd⟩
    rw [oddCore_linkGrp_eq_bot hL] at hle
    exact Subgroup.mem_bot.mp (hle ⟨y, hy, rfl⟩)

@[expose] noncomputable def linkLayerEquiv (hL : TightLargeHypR r n Y R S t) :
    ↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t) ≃* ↥(linkGrp R t) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_linkLayerHom hL)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (linkLayerHom'_surjective hL))

theorem linkLayerEquiv_mk (hL : TightLargeHypR r n Y R S t) (y : ↥(linkLayer R t)) :
    ((linkLayerEquiv hL (QuotientGroup.mk y) : ↥(linkGrp R t)) :
      SecQuot (CoreAssembly.conjClass (tightCore R)) t) = linkLayerHom hL y :=
  rfl

theorem isPGroup_secImg_core (hL : TightLargeHypR r n Y R S t) :
    IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R)) := by
  have h := TightLargeHypR.typeRFam hL
  have hΦ := h.secFam (x := t)
  have hK := secImg_mem (xMem_core hL)
  have hu := isUniqueInvolution_secImg h (xMem_core hL) hL.datum.isUniqueInvolution_core
  obtain ⟨z, hz, hz2, hsub⟩ := hΦ.cls.subnormal _ hK
  have hzt : z = QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))
        ⟨t, mem_layerY_of_isUniqueInvolution h (xMem_core hL) hL.datum.isUniqueInvolution_core⟩ :=
    (hu.unique z hz (by rw [← sq, ← hz2, pow_orderOf_eq_one])).resolve_left
      (fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by norm_num))
  have htop : Subgroup.centralizer ({z} : Set (SecQuot (CoreAssembly.conjClass (tightCore R)) t)) =
      ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [hzt, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (layerY_le_centralizer g.2))
  rw [htop] at hsub
  exact isPGroup_of_quot_oddCore_eq_bot (hΦ.twoGroup _ hK)
    (CFSG.ComponentClassification.OddCore.subnormal_corefree secQuot_oddCore_eq_bot _ hsub)

theorem secImg_mem_omegaNbr_secImg_core (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    secImg (CoreAssembly.conjClass (tightCore R)) t J ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R)) := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := id hJ
  have hTs : IsSylow2In T J := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hT hJΩ hTJ
  have hTt : T ≤ Subgroup.centralizer ({t} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hTN hx)
  have hJ' := hJ
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ' hu
  have htu : t ≠ u := fun e => hJ'.2.1 (eq_core_of_isUniqueInvolution hL hJΩ (e ▸ hu))
  exact secImg_mem_omegaNbr (xMem_core hL) (xMem_of_mem_omegaNbr_core hL hJ') hTs hTt hTN
    (secImg_ne h (xMem_core hL) (xMem_of_mem_omegaNbr_core hL hJ') ht hu ctu htu)

theorem linkGrp_le_centralizer (hL : TightLargeHypR r n Y R S t)
    (h2 : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) t J)) :
    linkGrp R t ≤ Subgroup.centralizer
      (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) : Set _) := by
  have hΦ := (TightLargeHypR.typeRFam hL).secFam (x := t)
  refine iSup₂_le fun Lb hLb => ?_
  obtain ⟨J, hJ, rfl⟩ := hLb
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact commutes_of_mem_omegaNbr_of_isPGroup hΦ.hyp (secImg_mem (xMem_core hL))
    (isPGroup_secImg_core hL) (h2 J hJ) (secImg_mem_omegaNbr_secImg_core hL hJ) k hk y hy

theorem commutator_mem_oddCoreOf_linkLayer (hL : TightLargeHypR r n Y R S t)
    (h2 : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) t J))
    {x : Y} (hx : x ∈ coreAt t (tightCore R)) {y : Y} (hy : y ∈ linkLayer R t) :
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
  have hcomm := Subgroup.mem_centralizer_iff.mp (linkGrp_le_centralizer hL h2 hyX) _ hxK
  rw [linkLayerHom_apply]
  have e : (⟨x * y * x⁻¹ * y⁻¹, linkLayer_le_layerY hL hc⟩ :
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) =
      ⟨x, hxL⟩ * ⟨y, hyL⟩ * ⟨x, hxL⟩⁻¹ * ⟨y, hyL⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
