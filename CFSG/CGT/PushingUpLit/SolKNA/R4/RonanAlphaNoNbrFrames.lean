module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrLink
public import CFSG.ClassicalInvolution.Q3.TL4S289GenC
public import CFSG.ClassicalInvolution.Q3.TL4StarSecOrb

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance.Bootstrap (rankTwoSpan le_rankTwoSpan_of_le_centralizer)
open CFSG.ClassicalInvolution.Disconnected (DConnected DEdgeless)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K'' : Subgroup Y} {u w : Y}


theorem closure_le_centralizer_of_starFrameAt_r (hL : TightLargeHypR r n Y R S t)
    {J K'' : Subgroup Y} {u w : Y} (hF : StarFrameAt R t J K'' u w) :
    Subgroup.closure ({t, u, w} : Set Y) ≤ Subgroup.centralizer ({t} : Set Y) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tu hL).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tw hL).symm

theorem starFrameAt_conj_r (hL : TightLargeHypR r n Y R S t) {J K'' : Subgroup Y} {u w : Y}
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

theorem starLinkStep_conj_r (hL : TightLargeHypR r n Y R S t) {A A' : Subgroup Y}
    (hs : StarLinkStep R t A A') {c : Y}
    (hc : c ∈ layerY (CoreAssembly.conjClass (tightCore R)) t) :
    StarLinkStep R t (conjSub c A) (conjSub c A') := by
  obtain ⟨K'', u, w, hF, g, hgt, hgB, rfl⟩ := hs
  have hct := layerY_le_centralizer hc
  have hctt : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hct, mul_inv_cancel_right]
  refine ⟨conjSub c K'', c * u * c⁻¹, c * w * c⁻¹, starFrameAt_conj_r hL hF hc, c * g * c⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hct hgt) (Subgroup.inv_mem _ hct), ?_, ?_⟩
  · have h1 := S289G.conj_mem_rankTwoSpan hgB c
    rwa [conjSub, map_conj_closure_three, hctt] at h1
  · rw [← conjSub_mul, ← conjSub_mul, show c * g * c⁻¹ * c = c * g by group]

theorem reflTransGen_of_mem_starMoveGrp_r (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    {u h : Y} (hh : h ∈ S289G.starMoveGrp R t J u) :
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
      exact hyJ.lift (conjSub x) fun _ _ hs => starLinkStep_conj_r hL hs hx
  exact key.2

theorem oddCoreOf_layerY_le_starMoveGrp_r (hL : TightLargeHypR r n Y R S t) {J K'' : Subgroup Y}
    {u w : Y} (hF : StarFrameAt R t J K'' u w) :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ≤ S289G.starMoveGrp R t J u := by
  refine le_trans (le_inf (Subgroup.map_subtype_le _) (LinkMove.oddCoreOf_layerY_le_rankTwoSpan hL
    (hF.isElemAbelian hL) (hF.natCard hL) (closure_le_centralizer_of_starFrameAt_r hL hF))) ?_
  exact le_iSup_of_le (⟨(K'', w), hF⟩ : {p : Subgroup Y × Y // StarFrameAt R t J p.1 u p.2})
    le_rfl

theorem exists_starFrameAt_of_pair_r (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
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
      omegaNbr (TL4.secFam (CoreAssembly.conjClass (tightCore R)) t)
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

theorem isUniqueInvolution_linkLayerHom'_r (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (huΛ : u ∈ linkLayer R t) :
    IsUniqueInvolution ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf
      (linkGrp R t)) (linkLayerHom' hL ⟨u, huΛ⟩) := by
  have h := isUniqueInvolution_subgroupOf (isUniqueInvolution_secImg
    (TightLargeHypR.typeRFam hL) (xMem_of_mem_omegaNbr_core hL hJ) hu) (le_linkGrp (t := t) hJ)
  convert h using 1
  exact Subtype.ext (linkLayerHom_apply hL ⟨u, huΛ⟩)

theorem linkLayer_le_starMoveGrp_r (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {K₁ : Subgroup Y} {w₁ : Y} (hF₁ : StarFrameAt R t J K₁ u w₁)
    (hgen : S289G.StarFrameGenAll (linkFam R t)
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))) :
    linkLayer R t ≤ S289G.starMoveGrp R t J u := by
  set π := linkLayerHom' hL with hπ
  have hπs : Function.Surjective π := linkLayerHom'_surjective hL
  have hodd2 : ¬ 2 ∣ Nat.card ↥π.ker := by
    rw [hπ, ker_linkLayerHom hL]
    exact Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _) ∘
      even_iff_two_dvd.mpr
  set M : Subgroup ↥(linkLayer R t) := (S289G.starMoveGrp R t J u).comap (linkLayer R t).subtype
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
    show (x : Y) ∈ S289G.starMoveGrp R t J u
    exact Subgroup.mem_iSup_of_mem (⟨(K'', w), hF⟩ : {p : Subgroup Y × Y //
      StarFrameAt R t J p.1 u p.2}) ⟨linkLayer_le_layerY hL x.2,
        le_rankTwoSpan_of_le_centralizer (LinkMove.closure_pair_mem hL (hF.isElemAbelian hL)
          (mem_closure_three_left t u w).1 hbB hb1 hbt) le_rfl hxC⟩
  have hker : π.ker ≤ M := by
    intro x hx
    have h1 : linkLayerHom hL x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [linkLayerHom_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact oddCoreOf_layerY_le_starMoveGrp_r hL hF₁
      (mem_oddCoreOf_iff.mpr ⟨linkLayer_le_layerY hL x.2, h1⟩)
  have huΛ := S289.u_mem_linkLayer hL hF₁
  have hou : orderOf (⟨u, huΛ⟩ : ↥(linkLayer R t)) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact Subtype.ext hu.sq)
      (fun h => hu.ne_one (congrArg Subtype.val h))
  have himg : M.map π = ⊤ := by
    rw [eq_top_iff, ← hgen _ (isUniqueInvolution_linkLayerHom'_r hL hJ hu huΛ)]
    refine sup_le ?_ (iSup₂_le fun L' hL' => iSup₂_le fun b hb => ?_)
    · rw [← CFSG.RankThree.OddKernel.map_centralizer_eq_of_odd π hπs hodd2 hou]
      exact Subgroup.map_mono (hpiece hF₁ ⟨u, huΛ⟩ (mem_closure_three_left t u w₁).2.1
        hu.ne_one ntu.symm)
    obtain ⟨K'', w, hF, hK⟩ := exists_starFrameAt_of_pair_r hL hJ hu hL'.1.1 hL'.1 hL'.2
    have hwΛ := S289.w_mem_linkLayer hL hF
    have hbw : b = π ⟨w, hwΛ⟩ := by
      have h1 := isUniqueInvolution_linkLayerHom'_r hL hF.memK hF.invK hwΛ
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

theorem reflTransGen_of_frameGen_r (hL : TightLargeHypR r n Y R S t) (htr : LinkTrans R t)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {u : Y} (hu : IsUniqueInvolution J u) {K₁ : Subgroup Y} {w₁ : Y}
    (hF₁ : StarFrameAt R t J K₁ u w₁)
    (hgen : S289G.StarFrameGenAll (linkFam R t)
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
  have hmem : (ν : Y) * g₁ ∈ S289G.starMoveGrp R t J u :=
    Subgroup.mul_mem _ (oddCoreOf_layerY_le_starMoveGrp_r hL hF₁ ⟨ν, hν, rfl⟩)
      (linkLayer_le_starMoveGrp_r hL hJ hu hF₁ hgen g₁.2)
  have h4 := reflTransGen_of_mem_starMoveGrp_r hL hmem
  rwa [conjSub_mul, ← hJeq] at h4


theorem exists_starFrameAt_of_link (hN : ∀ L ∈ linkFam R t, ∃ L' ∈ linkFam R t,
      L' ∈ omegaStarNbr (linkFam R t) L ∧ L' ∉ omegaNbr (linkFam R t) L)
    (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) : ∃ (K'' : Subgroup Y) (w : Y), StarFrameAt R t J K'' u w := by
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hcl := hΩ.conjInvariant
  have ht := hd.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨L', hL', hst, hnot⟩ := hN _ (subgroupOf_mem_linkRestrict hJ)
  obtain ⟨_, ⟨K'', hK'', rfl⟩, -, rfl⟩ := hL'
  have hst' := omegaStarNbr_secFam_of_link hL hJ hK'' hst
  have hnn : secImg (CoreAssembly.conjClass (tightCore R)) t K'' ∉
      omegaNbr (TL4.secFam (CoreAssembly.conjClass (tightCore R)) t)
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

theorem starFrame_orbit_r (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w) :
    ∃ g ∈ Subgroup.normalizer ((Subgroup.closure ({t, u, w} : Set Y) : Subgroup Y) : Set Y),
      g * t * g⁻¹ = t ∧ g * u * g⁻¹ = w ∧ g * w * g⁻¹ = u * w := by
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
  obtain ⟨gb, hga, hgb⟩ := starOrb_of_typeR ((typeRFam_coreLinkFam hL).restrict (linkGrp R t))
    (subgroupOf_mem_linkRestrict hF.memJ) hstL hnnL ha hb
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

theorem noGNbr_of_linkTrans_r (hL : TightLargeHypR r n Y R S t) (htr : LinkTrans R t)
    (hA : ¬ TriNbrAll R t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    NoGNbr R t J := by
  have h := TightLargeHypR.typeRFam hL
  obtain ⟨J₀, hJ₀, hbad⟩ := exists_noGNbr_of_not_triNbrAll hA
  obtain ⟨gb, hgb⟩ := htr _ (subgroupOf_mem_linkRestrict (t := t) hJ₀) _
    (subgroupOf_mem_linkRestrict (t := t) hJ)
  rw [Generic.conjSub_subgroupOf] at hgb
  have hle : conjSub (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J₀) ≤ linkGrp R t := by
    have h1 := conjSub_mono (n := (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t))
      (le_linkGrp (t := t) hJ₀)
    rwa [conjSub_eq_self_of_mem gb.2] at h1
  have h1 := Subgroup.subgroupOf_inj.mp hgb
  rw [inf_of_le_left hle, inf_of_le_left (le_linkGrp (t := t) hJ)] at h1
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective
    (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
  have hg₀C : (g₀ : Y) ∈ Subgroup.centralizer ({t} : Set Y) := layerY_le_centralizer g₀.2
  have h2 : secImg (CoreAssembly.conjClass (tightCore R)) t (conjSub (g₀ : Y) J₀) =
      secImg (CoreAssembly.conjClass (tightCore R)) t J := by
    rw [← conjSub_secImg]
    show conjSub (QuotientGroup.mk g₀) _ = _
    rw [hg₀]
    exact h1
  have hJ₀g := conjSub_mem_omegaNbr_core hL hJ₀ hg₀C
  obtain ⟨ν, -, hJeq⟩ := exists_conj_of_secImg_eq h (xMem_of_mem_omegaNbr_core hL hJ₀g)
    (xMem_of_mem_omegaNbr_core hL hJ) h2
  have hc : (ν : Y) * g₀ ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mul_mem _ (layerY_le_centralizer ν.2) hg₀C
  rw [hJeq, ← conjSub_mul]
  exact noGNbr_conj hL hbad hc

theorem mul_mem_center_link_r (hL : TightLargeHypR r n Y R S t) (htr : LinkTrans R t)
    (hA : ¬ TriNbrAll R t) :
    ∀ M ∈ linkFam R t, ∀ N ∈ omegaNbr (linkFam R t) M, ∀ m n' : ↥(linkGrp R t),
      IsUniqueInvolution M m → IsUniqueInvolution N n' →
        m * n' ∈ Subgroup.center ↥(linkGrp R t) := by
  intro M hM N hN m n' hm hn'
  have hNΦ := hN.1
  obtain ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩ := hM
  obtain ⟨_, ⟨K, hK, rfl⟩, -, rfl⟩ := hNΦ
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have hJx := xMem_of_mem_omegaNbr_core hL hJ
  have hKx := xMem_of_mem_omegaNbr_core hL hK
  have hnbr := omegaNbr_secFam_of_link hL hJ hK hN
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hJ.1
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hK.1
  have ha := isUniqueInvolution_secImg h hJx hu
  have hb := isUniqueInvolution_secImg h hKx hw
  have hc := isUniqueInvolution_secImg h (xMem_core hL) hd.isUniqueInvolution_core
  have e := mul_eq_of_noGNbr hL hJ (noGNbr_of_linkTrans_r hL htr hA hJ) hK hnbr ha hb hc
  have hm' : (m : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))
        ⟨u, mem_layerY_of_isUniqueInvolution h hJx hu⟩ :=
    congrArg Subtype.val (hm.eq (isUniqueInvolution_subgroupOf ha (le_linkGrp hJ)))
  have hn'' : (n' : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))
        ⟨w, mem_layerY_of_isUniqueInvolution h hKx hw⟩ :=
    congrArg Subtype.val (hn'.eq (isUniqueInvolution_subgroupOf hb (le_linkGrp hK)))
  set c : SecQuot (CoreAssembly.conjClass (tightCore R)) t := QuotientGroup.mk'
    (classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t))
    ⟨t, mem_layerY_of_isUniqueInvolution h (xMem_core hL) hd.isUniqueInvolution_core⟩ with hcdef
  have hcZ : ∀ z : SecQuot (CoreAssembly.conjClass (tightCore R)) t, c * z = z * c := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) z
    rw [hcdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (layerY_le_centralizer y.2)).symm
  have key : ((m * n' : ↥(linkGrp R t)) : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      c := by
    rw [Subgroup.coe_mul, hm', hn'', e, ← mul_assoc, ← hcZ, mul_assoc, ha.sq, mul_one]
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  have e1 : ((x * (m * n') : ↥(linkGrp R t)) : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      (x : SecQuot (CoreAssembly.conjClass (tightCore R)) t) * c := by
    rw [Subgroup.coe_mul, key]
  have e2 : ((m * n' * x : ↥(linkGrp R t)) : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      c * (x : SecQuot (CoreAssembly.conjClass (tightCore R)) t) := by
    rw [Subgroup.coe_mul, key]
  rw [e1, e2]
  exact (hcZ _).symm


theorem star_nbr_all_of_trans {X : Type} [Group X] {Φ : Set (Subgroup X)} (hcl : ConjInvariant Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    (h1 : ∃ M ∈ Φ, ∃ N ∈ Φ, N ∈ omegaStarNbr Φ M ∧ N ∉ omegaNbr Φ M) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  obtain ⟨M, hM, N, hN, hst, hn⟩ := h1
  intro L hL
  obtain ⟨g, hg⟩ := htr M hM L hL
  refine ⟨conjSub g N, hcl g N hN, ?_, ?_⟩
  · have h2 := Asc77.omegaStarNbr_conj hcl hst g
    rwa [hg] at h2
  · intro h
    apply hn
    rw [← hg] at h
    have h2 := Asc77.omegaNbr_conj hcl h g⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2

theorem starFrameGenAll_of_exitLU {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (h : TypeRFam r Φ) (hN : ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L)
    {R' : Subgroup X} {S' : Sylow 2 ↥R'} {z : X} (hd : TightDatum R' S' z) (hE : ExitLU R' S' z)
    (heq : CoreAssembly.conjClass (tightCore R') = Φ) {L : Subgroup X} (hL : L ∈ Φ) :
    S289G.StarFrameGenAll Φ L := by
  obtain ⟨L', hL'Φ, hst, hn⟩ := hN L hL
  obtain ⟨b, hb⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL'Φ
  refine S289G.StarFrameGenAll.of_pair hst hn hb fun a ha => ?_
  obtain ⟨L₀, -, -, -, -, -, hgenE⟩ := hE
  have hz := hd.isUniqueInvolution_core
  have hLc : ∃ g : X, conjSub g (tightCore R') = L := by
    have h1 : L ∈ CoreAssembly.conjClass (tightCore R') := by rw [heq]; exact hL
    exact h1
  have hL'c : ∃ g : X, conjSub g (tightCore R') = L' := by
    have h1 : L' ∈ CoreAssembly.conjClass (tightCore R') := by rw [heq]; exact hL'Φ
    exact h1
  obtain ⟨g, hg⟩ := hLc
  obtain ⟨g', hg'⟩ := hL'c
  have hag : a = g * z * g⁻¹ := ha.eq (hg ▸ hz.conj g)
  have hbg : b = g' * z * g'⁻¹ := hb.eq (hg' ▸ hz.conj g')
  have hab := S289G.mul_comm_of_mem_omegaStarNbr h.hyp hst ha hb
  have hne : a ≠ b := fun e => hst.2.1 (h.noTwins L hL L' ⟨hL'Φ, a, ha, e ▸ hb⟩)
  set s := g⁻¹ * b * g with hs
  have hzs : z * s = s * z := by
    have e1 : z = g⁻¹ * a * g := by rw [hag]; group
    rw [hs, e1]
    calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [hab]
      _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group
  have hsz : s ≠ z := fun e => hne (by rw [hag, ← e, hs]; group)
  have hsconj : ∃ k : X, s = k * z * k⁻¹ := ⟨g⁻¹ * g', by rw [hs, hbg]; group⟩
  have hgen' := hgenE s hzs hsz hsconj
  have h2 := S289G.sup_centralizer_conj hgen' g
  rw [← hag, show g * s * g⁻¹ = b by rw [hs]; group] at h2
  rw [eq_top_iff, ← h2]
  exact le_sup_left

theorem star_frames_of_shape (hL : TightLargeHypR r n Y R S t) (hA : ¬ TriNbrAll R t)
    (htr : LinkTrans R t) (hnc : ¬ DConnected (linkFam R t)) (hcase : LinkWR R t ∨ LinkSR R t) :
    (∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → ∃ (K'' : Subgroup Y) (w : Y), StarFrameAt R t J K'' u w) ∧
    (∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (StarLinkStep R t) J J') := by
  classical
  have hΦ : TypeRFam r (linkFam R t) := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hgenΦ : omegaGen (linkFam R t) = ⊤ := omegaGen_linkRestrict
  have hcl := hΦ.hyp.conjInvariant
  have hN : ∀ L ∈ linkFam R t, ∃ L' ∈ linkFam R t,
      L' ∈ omegaStarNbr (linkFam R t) L ∧ L' ∉ omegaNbr (linkFam R t) L := by
    rcases hcase with ⟨-, hDS⟩ | ⟨hDE, ⟨M, hM, N, hN0⟩, -⟩
    · exact star_nbr_all_of_trans hcl htr (exists_star_not_nbr_of_dstarConnected hDS hnc)
    · exact star_nbr_all_of_trans hcl htr
        ⟨M, hM, N, hN0.1, hN0, fun h => hDE M hM N hN0.1 (Or.inl h)⟩
  refine ⟨fun J hJ u hu => exists_starFrameAt_of_link hN hL hJ hu, ?_⟩
  intro J hJ J' hJ'
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hJ.1
  obtain ⟨K₁, w₁, hF₁⟩ := exists_starFrameAt_of_link hN hL hJ hu
  have hJm := subgroupOf_mem_linkRestrict (t := t) hJ
  have hgenAll : S289G.StarFrameGenAll (linkFam R t)
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) := by
    rcases hcase with ⟨-, hDS⟩ | ⟨-, -, R', S', z', -, hd, hE, hfam⟩
    · exact S289G.starFrameGenAll_of_dstarConnected hΦ hgenΦ hDS (mul_mem_center_link_r hL htr hA)
        hJm
    · exact starFrameGenAll_of_exitLU hΦ hN hd hE hfam hJm
  exact reflTransGen_of_frameGen_r hL htr hJ hu hF₁ hgenAll hJ'

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
