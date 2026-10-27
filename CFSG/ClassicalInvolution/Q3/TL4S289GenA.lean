module

public import CFSG.ClassicalInvolution.Q3.TL4S289GenB
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Mv
public import CFSG.ClassicalInvolution.Q3.TL4S289Lnk
public import CFSG.ClassicalInvolution.Q3.TL4LinkCases
public import CFSG.RankThree.OddKernel.FixedPlaneKernel

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance.Bootstrap (rankTwoSpan le_rankTwoSpan_of_le_centralizer)
open CFSG.ClassicalInvolution.Disconnected (DConnected)

namespace S289G

section Span

variable {G : Type} [Group G]

theorem conj_mem_rankTwoSpan {B : Subgroup G} {g : G} (hg : g ∈ rankTwoSpan B) (c : G) :
    c * g * c⁻¹ ∈ rankTwoSpan (conjSub c B) := by
  have key : (rankTwoSpan B).map (MulAut.conj c).toMonoidHom ≤ rankTwoSpan (conjSub c B) := by
    unfold rankTwoSpan
    rw [Subgroup.map_iSup]
    refine iSup_le fun F => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hF => ?_
    refine le_iSup₂_of_le (conjSub c F) ⟨conjSub_mono hF.1, ?_⟩ ?_
    · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact hF.2
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ Subgroup.centralizer (F : Set G) := hy
      rw [Subgroup.mem_centralizer_iff] at hy' ⊢
      intro f hf
      rw [SetLike.mem_coe, mem_conjSub_iff] at hf
      have e := hy' _ hf
      show f * (c * y * c⁻¹) = c * y * c⁻¹ * f
      calc f * (c * y * c⁻¹) = c * ((c⁻¹ * f * c) * y) * c⁻¹ := by group
        _ = c * (y * (c⁻¹ * f * c)) * c⁻¹ := by rw [e]
        _ = c * y * c⁻¹ * f := by group
  exact key ⟨g, hg, rfl⟩

end Span

section Defs

variable {Y : Type} [Group Y]

@[expose] noncomputable def starMoveGrp (R : Subgroup Y) (t : Y) (J : Subgroup Y) (u : Y) :
    Subgroup Y :=
  ⨆ p : {p : Subgroup Y × Y // StarFrameAt R t J p.1 u p.2},
    layerY (CoreAssembly.conjClass (tightCore R)) t ⊓
      rankTwoSpan (Subgroup.closure ({t, u, p.1.2} : Set Y))

end Defs

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem closure_le_centralizer_of_starFrameAt (hL : TightLargeHypR 3 n Y R S t)
    {J K'' : Subgroup Y} {u w : Y} (hF : StarFrameAt R t J K'' u w) :
    Subgroup.closure ({t, u, w} : Set Y) ≤ Subgroup.centralizer ({t} : Set Y) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tu hL).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tw hL).symm

theorem starFrameAt_conj (hL : TightLargeHypR 3 n Y R S t) {J K'' : Subgroup Y} {u w : Y}
    (hF : StarFrameAt R t J K'' u w) {c : Y}
    (hc : c ∈ layerY (CoreAssembly.conjClass (tightCore R)) t) :
    StarFrameAt R t (conjSub c J) (conjSub c K'') (c * u * c⁻¹) (c * w * c⁻¹) := by
  have hcl := hL.datum.hypOmegaGen.conjInvariant
  have hct := layerY_le_centralizer hc
  have hsc := ((TightLargeHypR.typeRFam hL).secFam (x := t)).hyp.conjInvariant
  set cb := QuotientGroup.mk' (classicalInvolutionOddCore
    ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨c, hc⟩ with hcb
  have eJ : secImg (CoreAssembly.conjClass (tightCore R)) t (conjSub c J) =
      conjSub cb (secImg (CoreAssembly.conjClass (tightCore R)) t J) :=
    (conjSub_secImg (Ω := CoreAssembly.conjClass (tightCore R)) (x := t) ⟨c, hc⟩ J).symm
  have eK : secImg (CoreAssembly.conjClass (tightCore R)) t (conjSub c K'') =
      conjSub cb (secImg (CoreAssembly.conjClass (tightCore R)) t K'') :=
    (conjSub_secImg (Ω := CoreAssembly.conjClass (tightCore R)) (x := t) ⟨c, hc⟩ K'').symm
  refine ⟨conjSub_mem_omegaNbr_core hL hF.memJ hct, conjSub_mem_omegaNbr_core hL hF.memK hct,
    Asc77.omegaStarNbr_conj hcl hF.star c, fun h' => hF.notNbr ?_, hF.invJ.conj c,
    hF.invK.conj c, ?_, fun h' => hF.secNotNbr ?_⟩
  · have h2 := Asc77.omegaNbr_conj hcl h' c⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
  · rw [eJ, eK]
    exact Asc77.omegaStarNbr_conj hsc hF.secStar cb
  · rw [eJ, eK] at h'
    have h2 := Asc77.omegaNbr_conj hsc h' cb⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2

theorem starLinkStep_conj (hL : TightLargeHypR 3 n Y R S t) {A A' : Subgroup Y}
    (hs : StarLinkStep R t A A') {c : Y}
    (hc : c ∈ layerY (CoreAssembly.conjClass (tightCore R)) t) :
    StarLinkStep R t (conjSub c A) (conjSub c A') := by
  obtain ⟨K'', u, w, hF, g, hgt, hgB, rfl⟩ := hs
  have hct := layerY_le_centralizer hc
  have hctt : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hct, mul_inv_cancel_right]
  refine ⟨conjSub c K'', c * u * c⁻¹, c * w * c⁻¹, starFrameAt_conj hL hF hc, c * g * c⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hct hgt) (Subgroup.inv_mem _ hct), ?_, ?_⟩
  · have h1 := conj_mem_rankTwoSpan hgB c
    rwa [conjSub, map_conj_closure_three, hctt] at h1
  · rw [← conjSub_mul, ← conjSub_mul, show c * g * c⁻¹ * c = c * g by group]

theorem reflTransGen_of_mem_starMoveGrp (hL : TightLargeHypR 3 n Y R S t) {J : Subgroup Y}
    {u h : Y} (hh : h ∈ starMoveGrp R t J u) :
    Relation.ReflTransGen (StarLinkStep R t) J (conjSub h J) := by
  have hh' : h ∈ ⨆ p : {p : Subgroup Y × Y // StarFrameAt R t J p.1 u p.2},
      layerY (CoreAssembly.conjClass (tightCore R)) t ⊓
        rankTwoSpan (Subgroup.closure ({t, u, p.1.2} : Set Y)) := hh
  have key : h ∈ layerY (CoreAssembly.conjClass (tightCore R)) t ∧
      Relation.ReflTransGen (StarLinkStep R t) J (conjSub h J) := by
    refine Subgroup.iSup_induction _ (C := fun x => x ∈ layerY (CoreAssembly.conjClass
      (tightCore R)) t ∧ Relation.ReflTransGen (StarLinkStep R t) J (conjSub x J)) hh' ?_ ?_ ?_
    · intro p x hx
      exact ⟨hx.1, Relation.ReflTransGen.single ⟨p.1.1, u, p.1.2, p.2, x,
        layerY_le_centralizer hx.1, hx.2, rfl⟩⟩
    · exact ⟨Subgroup.one_mem _, by rw [conjSub_one]⟩
    · rintro x y ⟨hx, hxJ⟩ ⟨hy, hyJ⟩
      refine ⟨Subgroup.mul_mem _ hx hy, hxJ.trans ?_⟩
      rw [conjSub_mul]
      exact hyJ.lift (conjSub x) fun _ _ hs => starLinkStep_conj hL hs hx
  exact key.2

theorem oddCoreOf_layerY_le_starMoveGrp (hL : TightLargeHypR 3 n Y R S t) {J K'' : Subgroup Y}
    {u w : Y} (hF : StarFrameAt R t J K'' u w) :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ≤ starMoveGrp R t J u := by
  refine le_trans (le_inf (Subgroup.map_subtype_le _) (LinkMove.oddCoreOf_layerY_le_rankTwoSpan hL
    (hF.isElemAbelian hL) (hF.natCard hL) (closure_le_centralizer_of_starFrameAt hL hF))) ?_
  exact le_iSup_of_le (⟨(K'', w), hF⟩ : {p : Subgroup Y × Y // StarFrameAt R t J p.1 u p.2})
    le_rfl

theorem exists_starFrameAt_of_pair (hL : TightLargeHypR 3 n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {L' : Subgroup ↥(linkGrp R t)} (hL' : L' ∈ linkFam R t)
    (hst : L' ∈ omegaStarNbr (linkFam R t)
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)))
    (hnot : L' ∉ omegaNbr (linkFam R t)
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))) :
    ∃ (K'' : Subgroup Y) (w : Y), StarFrameAt R t J K'' u w ∧
      (secImg (CoreAssembly.conjClass (tightCore R)) t K'').subgroupOf (linkGrp R t) = L' := by
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hcl := hΩ.conjInvariant
  have ht := hd.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
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
    have h1 := Asc77.omegaStarNbr_conj hcl hstY c
    have e : conjSub c (conjSub (ν : Y) J) = J := by
      rw [hcdef, Subgroup.coe_inv, conjSub_inv_conjSub]
    rwa [e] at h1
  refine ⟨_, _, ⟨hJ, hK3, hstar3, fun hKJ => ?_, hu, hw3, by rw [hsec]; exact hst', by
    rw [hsec]; exact hnn⟩, by rw [hsec]⟩
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

theorem isUniqueInvolution_linkLayerHom' (hL : TightLargeHypR 3 n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (huΛ : u ∈ linkLayer R t) :
    IsUniqueInvolution ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf
      (linkGrp R t)) (linkLayerHom' hL ⟨u, huΛ⟩) := by
  have h := isUniqueInvolution_subgroupOf (isUniqueInvolution_secImg
    (TightLargeHypR.typeRFam hL) (xMem_of_mem_omegaNbr_core hL hJ) hu) (le_linkGrp (t := t) hJ)
  convert h using 1
  exact Subtype.ext (linkLayerHom_apply hL ⟨u, huΛ⟩)

theorem linkLayer_le_starMoveGrp (hL : TightLargeHypR 3 n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {K₁ : Subgroup Y} {w₁ : Y} (hF₁ : StarFrameAt R t J K₁ u w₁)
    (hgen : StarFrameGenAll (linkFam R t)
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))) :
    linkLayer R t ≤ starMoveGrp R t J u := by
  set π := linkLayerHom' hL with hπ
  have hπs : Function.Surjective π := linkLayerHom'_surjective hL
  have hodd2 : ¬ 2 ∣ Nat.card ↥π.ker := by
    rw [hπ, ker_linkLayerHom hL]
    exact Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _) ∘
      even_iff_two_dvd.mpr
  set M : Subgroup ↥(linkLayer R t) := (starMoveGrp R t J u).comap (linkLayer R t).subtype
    with hM
  have ntu : t ≠ u := fun e => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (e ▸ hu))
  have hpiece : ∀ {K'' : Subgroup Y} {w : Y}, StarFrameAt R t J K'' u w →
      ∀ b : ↥(linkLayer R t), (b : Y) ∈ Subgroup.closure ({t, u, w} : Set Y) → (b : Y) ≠ 1 →
        (b : Y) ≠ t → Subgroup.centralizer ({b} : Set ↥(linkLayer R t)) ≤ M := by
    intro K'' w hF b hbB hb1 hbt x hx
    have hxC : (x : Y) ∈ Subgroup.centralizer ((Subgroup.closure ({t, (b : Y)} : Set Y) :
        Subgroup Y) : Set Y) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      rintro s (rfl | rfl)
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer x.2)).symm
      · exact (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)).symm
    show (x : Y) ∈ starMoveGrp R t J u
    exact Subgroup.mem_iSup_of_mem (⟨(K'', w), hF⟩ : {p : Subgroup Y × Y //
      StarFrameAt R t J p.1 u p.2}) ⟨linkLayer_le_layerY hL x.2,
        le_rankTwoSpan_of_le_centralizer (LinkMove.closure_pair_mem hL (hF.isElemAbelian hL)
          (mem_closure_three_left t u w).1 hbB hb1 hbt) le_rfl hxC⟩
  have hker : π.ker ≤ M := by
    intro x hx
    have h1 : linkLayerHom hL x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [linkLayerHom_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact oddCoreOf_layerY_le_starMoveGrp hL hF₁
      (mem_oddCoreOf_iff.mpr ⟨linkLayer_le_layerY hL x.2, h1⟩)
  have huΛ := S289.u_mem_linkLayer hL hF₁
  have hou : orderOf (⟨u, huΛ⟩ : ↥(linkLayer R t)) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact Subtype.ext hu.sq)
      (fun h => hu.ne_one (congrArg Subtype.val h))
  have himg : M.map π = ⊤ := by
    rw [eq_top_iff, ← hgen _ (isUniqueInvolution_linkLayerHom' hL hJ hu huΛ)]
    refine sup_le ?_ (iSup₂_le fun L' hL' => iSup₂_le fun b hb => ?_)
    · rw [← CFSG.RankThree.OddKernel.map_centralizer_eq_of_odd π hπs hodd2 hou]
      exact Subgroup.map_mono (hpiece hF₁ ⟨u, huΛ⟩ (mem_closure_three_left t u w₁).2.1
        hu.ne_one ntu.symm)
    obtain ⟨K'', w, hF, hK⟩ := exists_starFrameAt_of_pair hL hJ hu hL'.1.1 hL'.1 hL'.2
    have hwΛ := S289.w_mem_linkLayer hL hF
    have hbw : b = π ⟨w, hwΛ⟩ := by
      have h1 := isUniqueInvolution_linkLayerHom' hL hF.memK hF.invK hwΛ
      rw [hK] at h1
      exact hb.eq h1
    have hm3 := mem_closure_three_left t u w
    have hnc := hF.not_mem_closure hL
    have huw := hF.comm_uw hL
    have hwt : w ≠ t := fun e => hnc (e ▸ Subgroup.subset_closure (by simp))
    have hw1 : w ≠ 1 := hF.invK.ne_one
    have huwB := Subgroup.mul_mem _ hm3.2.1 hm3.2.2
    have huw1 : u * w ≠ 1 := fun e => hnc (by
      rw [show w = u⁻¹ * (u * w) by group, e, mul_one]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    have huwt : u * w ≠ t := fun e => hnc (by
      rw [show w = u⁻¹ * (u * w) by group, e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp)))
    have how : orderOf (⟨w, hwΛ⟩ : ↥(linkLayer R t)) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact Subtype.ext hF.invK.sq)
        (fun h => hw1 (congrArg Subtype.val h))
    have houw : orderOf (⟨u, huΛ⟩ * ⟨w, hwΛ⟩ : ↥(linkLayer R t)) = 2 :=
      orderOf_eq_prime (by
        rw [sq]
        exact Subtype.ext (show u * w * (u * w) = 1 by
          rw [mul_mul_self_of_comm huw, hu.sq, hF.invK.sq, one_mul]))
        (fun h => huw1 (congrArg Subtype.val h))
    refine sup_le ?_ ?_
    · rw [hbw, ← CFSG.RankThree.OddKernel.map_centralizer_eq_of_odd π hπs hodd2 how]
      exact Subgroup.map_mono (hpiece hF ⟨w, hwΛ⟩ hm3.2.2 hw1 hwt)
    · rw [hbw, ← map_mul, ← CFSG.RankThree.OddKernel.map_centralizer_eq_of_odd π hπs hodd2 houw]
      exact Subgroup.map_mono (hpiece hF (⟨u, huΛ⟩ * ⟨w, hwΛ⟩) huwB huw1 huwt)
  intro y hy
  have hyM : (⟨y, hy⟩ : ↥(linkLayer R t)) ∈ M := by
    rw [← Subgroup.comap_map_eq_self hker, himg]
    exact Subgroup.mem_top _
  exact hyM

theorem reflTransGen_of_frameGen (hL : TightLargeHypR 3 n Y R S t) (htr : LinkTrans R t)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {u : Y} (hu : IsUniqueInvolution J u) {K₁ : Subgroup Y} {w₁ : Y}
    (hF₁ : StarFrameAt R t J K₁ u w₁)
    (hgen : StarFrameGenAll (linkFam R t)
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)))
    {J' : Subgroup Y} (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    Relation.ReflTransGen (StarLinkStep R t) J J' := by
  have h := TightLargeHypR.typeRFam hL
  obtain ⟨gb, hgb⟩ := htr _ (subgroupOf_mem_linkRestrict (t := t) hJ) _
    (subgroupOf_mem_linkRestrict (t := t) hJ')
  rw [Generic.conjSub_subgroupOf] at hgb
  have hle : conjSub (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J) ≤ linkGrp R t := by
    have h1 := conjSub_mono (n := (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t))
      (le_linkGrp (t := t) hJ)
    rwa [conjSub_eq_self_of_mem gb.2] at h1
  have h1 := Subgroup.subgroupOf_inj.mp hgb
  rw [inf_of_le_left hle, inf_of_le_left (le_linkGrp (t := t) hJ')] at h1
  obtain ⟨g₁, hg₁⟩ := linkLayerHom'_surjective hL gb
  have hg₁Y := linkLayer_le_layerY hL g₁.2
  have h2 : secImg (CoreAssembly.conjClass (tightCore R)) t (conjSub (g₁ : Y) J) =
      secImg (CoreAssembly.conjClass (tightCore R)) t J' := by
    have e : QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨g₁, hg₁Y⟩ =
          (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t) := by
      rw [← hg₁]
      rfl
    have h3 := conjSub_secImg (Ω := CoreAssembly.conjClass (tightCore R)) (x := t)
      ⟨(g₁ : Y), hg₁Y⟩ J
    rw [e, h1] at h3
    exact h3.symm
  have hJg := conjSub_mem_omegaNbr_core hL hJ (linkLayerAt_le_centralizer g₁.2)
  obtain ⟨ν, hν, hJeq⟩ := exists_conj_of_secImg_eq h (xMem_of_mem_omegaNbr_core hL hJg)
    (xMem_of_mem_omegaNbr_core hL hJ') h2
  have hmem : (ν : Y) * g₁ ∈ starMoveGrp R t J u :=
    Subgroup.mul_mem _ (oddCoreOf_layerY_le_starMoveGrp hL hF₁ ⟨ν, hν, rfl⟩)
      (linkLayer_le_starMoveGrp hL hJ hu hF₁ hgen g₁.2)
  have h4 := reflTransGen_of_mem_starMoveGrp hL hmem
  rwa [conjSub_mul, ← hJeq] at h4

@[expose] def TightStar289FrameGenR (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR 3 n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkS3S4 R t →
        ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          StarFrameGenAll (linkFam R t)
            ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))

theorem tightStar289GenR_of_frameGen (hN : SecIdStarNbrId3) (hg : TightStar289FrameGenR n) :
    TightStar289GenR 3 n := by
  intro Y _ _ R S t hL hc hA hcase J hJ J' hJ'
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hJ.1
  obtain ⟨K₁, w₁, hF₁⟩ := exists_starFrameAt_of_secId hN hL hcase hJ hu
  exact reflTransGen_of_frameGen hL hcase.1 hJ hu hF₁ (hg Y R S t hL hc hA hcase J hJ) hJ'

end Cit3

end S289G

end CFSG.ClassicalInvolution.Q3.TL4
