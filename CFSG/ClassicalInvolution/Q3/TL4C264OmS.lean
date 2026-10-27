module

public import CFSG.ClassicalInvolution.Q3.TL4C264OmZ
public import CFSG.ClassicalInvolution.Q3.TL4Conn264B
public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4G
public import CFSG.ClassicalInvolution.Q3.TL4C264OmDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame (CentOmega3)
open CFSG.Blueprint

theorem orbGrp_le_iSup_conjSub {Q : Type} [Group Q] (Φ : Set (Subgroup Q)) (K : Subgroup Q) :
    Vtx.orbGrp Φ K ≤ ⨆ g : Q, conjSub g K :=
  iSup_le fun g => le_iSup (fun g : Q => conjSub g K) (g : Q)

theorem secAct_mk_eq_of_commute {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}
    (hcl : ConjInvariant Ω) {y : G} (hy : y ∈ Subgroup.centralizer ({x} : Set G))
    (w : ↥(layerY Ω x)) (hyw : y * (w : G) = w * y) :
    secAct hcl hy (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) w) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) w :=
  s26Act_mk (layerY Ω x) ⟨y, mem_normalizer_layerY hcl hy⟩ w w (by
    show (w : G) = y * w * y⁻¹
    rw [hyw, mul_inv_cancel_right])

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.twinBase3_secFam (h4 : Thm4RBelow 3 n)
    (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hO2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z)
    (hzY : z ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))
    (htY : t ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) :
    TwinBase3 (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd))
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J)
      (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨z, hzY⟩)
      (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨t, htY⟩) := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ := h.secFam (x := z * t)
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  have hzb : IsUniqueInvolution (secImg Ω (z * t) K)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨z, hzY⟩) :=
    isUniqueInvolution_secImg h hs.xMem_K hs.hz
  have htb : IsUniqueInvolution (secImg Ω (z * t) J)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨t, htY⟩) :=
    isUniqueInvolution_secImg h hs.xMem_J hs.ht
  refine ⟨hΦ, secQuot_oddCore_eq_bot, hKΦ, hcj, hzb, htb, fun e => ?_,
    hs.mk_mul_mk_mem_center hzY htY, ?_, ?_⟩
  · apply hs.secImg_J_mem_omegaNbr.2.1
    refine hΦ.noTwins _ hKΦ _ ⟨hJΦ, _, hzb, ?_⟩
    rw [e]
    exact htb
  · rw [eq_top_iff, ← hs.secOrb_eq_top_of_E4 h4 hE hcj]
    exact orbGrp_le_iSup_conjSub _ _
  · rintro ⟨P, hPn, hP2, hzP⟩
    apply hO2
    refine ⟨P.subgroupOf (secOrb Ω K (z * t)), inferInstance, hP2.comap_subtype, fun c hc => ?_⟩
    rw [secCyc_eq_zpowers hzY] at hc
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [Subgroup.mem_subgroupOf, ← hm]
    exact P.zpow_mem hzP m

theorem TightStd8R.noThreeOver2_secFam (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    NoThreeOver2 (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)) := by
  intro M₁ h₁ M₂ h₂ M₃ h₃ h12 h13 h23 P hP hc₁ hc₂
  refine le_of_not_gt fun hc₃ => ?_
  obtain ⟨L₁, hL₁, rfl⟩ := mem_secFam_iff.mp h₁
  obtain ⟨L₂, hL₂, rfl⟩ := mem_secFam_iff.mp h₂
  obtain ⟨L₃, hL₃, rfl⟩ := mem_secFam_iff.mp h₃
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hL₁ hL₂ hL₃ h12 h13 h23 hP hc₁ hc₂ hc₃

theorem TightStd8R.isSylow2In_secImg_R (hs : TightStd8R 3 n Rd Sd z J S R T W t) :
    IsSylow2In ((R.subgroupOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))).map
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)))))
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)) := by
  have hXK := hs.xMem_K
  have hRsyl : IsSylow2In R (tightCore Rd) :=
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.hyp hs.mem hs.hR.1 hs.hR.2.1
  have hRc : IsSylow2In R (coreAt (z * t) (tightCore Rd)) :=
    (isSylow2In_coreAt_iff hXK).mpr ⟨hRsyl, Q3CL.T8R.Loc.le_centralizer_mul hs.toStd8Core⟩
  exact isSylow2In_map_mk odd_natCard_oddCore_layerY (hRc.subgroupOf (coreAt_le_layerY hXK))

theorem TightStd8R.twinSigmaOut3_secAct (h4 : Thm4RBelow 3 n) (hLC : TightLambdaCommR 3 n)
    (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hΛp : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hO2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z)
    (hzY : z ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))
    (htY : t ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) {t₁ : Y}
    (ht1C : t₁ ∈ Subgroup.centralizer ({z * t} : Set Y)) (ht1sq : t₁ * t₁ = 1) (hne : t₁ ≠ t)
    (htt1 : t * t₁ = t₁ * t) (hcommR : ∀ x ∈ R, x * t₁ = t₁ * x) (hnJ : conjSub t₁ J = J)
    {J₁ : Subgroup Y} (hJ₁ : J₁ ∈ CoreAssembly.conjClass (tightCore Rd))
    (hJ₁X : J₁ ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hJ₁t : IsUniqueInvolution J₁ t₁) :
    TwinSigmaOut3 (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd))
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J)
      (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨z, hzY⟩)
      (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨t, htY⟩)
      (secAct hs.hyp.conjInvariant ht1C) := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have hcl : ConjInvariant Ω := hs.hyp.conjInvariant
  have hyY1 := mem_normalizer_layerY hcl ht1C
  refine ⟨hs.twinBase3_secFam h4 hE hcj hO2 hzY htY, fun M hM => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM
    rw [← secImg_conjSub_eq_map hcl ht1C L]
    exact secImg_mem (XMem.conj' hcl hL ht1C)
  · show s26Act (layerY Ω (z * t)) ⟨t₁, hyY1⟩ * s26Act (layerY Ω (z * t)) ⟨t₁, hyY1⟩ = 1
    rw [← map_mul]
    have e : (⟨t₁, hyY1⟩ * ⟨t₁, hyY1⟩ : ↥(Subgroup.normalizer
        ((layerY Ω (z * t) : Subgroup Y) : Set Y))) = 1 := Subtype.ext ht1sq
    rw [e, map_one]
  · refine ⟨_, hs.isSylow2In_secImg_R, fun w hw => ?_⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hw
    exact secAct_mk_eq_of_commute hcl ht1C r (hcommR r (Subgroup.mem_subgroupOf.mp hr)).symm
  · have e := secImg_conjSub_eq_map hcl ht1C J
    rw [hnJ] at e
    exact e.symm
  · have hKX := hs.not_le_omegaNbrGen_of_ne_top (tightSecNbrGenR_of_comm hLC)
      (ne_top_of_le_ne_top hΛp le_sup_right)
    have hnt := hs.not_trivial_on_secImg_J_of_not_le hKX hE ht1C ht1sq hne htt1 hnJ hJ₁ hJ₁X hJ₁t
    by_contra hfix
    refine hnt fun kb hkb => ?_
    have e : secAct hs.hyp.conjInvariant ht1C kb = kb := by
      by_contra hne'
      exact hfix ⟨kb, hkb, hne'⟩
    rw [e, mul_inv_cancel]
    exact (oddCoreOf _).one_mem

theorem TightStd8R.exists_twinSigmaOut3 (h4 : Thm4RBelow 3 n) (hLC : TightLambdaCommR 3 n)
    (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hΛp : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hO2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z)
    (hzY : z ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))
    (htY : t ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) :
    ∃ (t₁ : Y) (ht1C : t₁ ∈ Subgroup.centralizer ({z * t} : Set Y)),
      (∃ g ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
        g⁻¹ * t * g = t₁) ∧
      (∃ J₁ ∈ CoreAssembly.conjClass (tightCore Rd),
        J₁ ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
          IsUniqueInvolution J₁ t₁) ∧
      TwinSigmaOut3 (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
        (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd))
        (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J)
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨z, hzY⟩)
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨t, htY⟩)
        (secAct hs.hyp.conjInvariant ht1C) := by
  obtain ⟨t₁, hg, ht1sq, -, hne, htt1, hzt1, hcommR, hnJ, -, -, J₁, hJ₁, hJ₁X, hJ₁t⟩ :=
    hs.exists_good_involution_E4_conj_of_ne_top hLC hΛp hE
  have ht1C : t₁ ∈ Subgroup.centralizer ({z * t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t₁ * (z * t) = (t₁ * z) * t := by group
      _ = (z * t₁) * t := by rw [hzt1]
      _ = z * (t₁ * t) := by group
      _ = z * (t * t₁) := by rw [htt1]
      _ = z * t * t₁ := by group
  exact ⟨t₁, ht1C, hg, ⟨J₁, hJ₁, hJ₁X, hJ₁t⟩, hs.twinSigmaOut3_secAct h4 hLC hΛp hE hcj hO2 hzY
    htY ht1C ht1sq hne htt1 hcommR hnJ hJ₁ hJ₁X hJ₁t⟩

theorem TightStd8R.secCyc_mul_eq_zpowers (_hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hzY : z ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))
    (htY : t ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) :
    secCyc (CoreAssembly.conjClass (tightCore Rd)) (z * t) (z * t) = Subgroup.zpowers
      (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨z, hzY⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) ⟨t, htY⟩) := by
  rw [secCyc_eq_zpowers ((layerY _ (z * t)).mul_mem hzY htY), ← map_mul]
  rfl

theorem TightStd8R.exists_psl43_of_models (hRk : Model264Rank3) (h1521 : Model1521Twin3)
    (h4 : Thm4RBelow 3 n) (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hω : SecTwinOmega (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))
    {k k' : SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)}
    {σ : MulAut (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))}
    (hσ : TwinSigmaOut3 (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd))
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J) k k' σ)
    (hkk : secCyc (CoreAssembly.conjClass (tightCore Rd)) (z * t) (z * t) =
      Subgroup.zpowers (k * k')) :
    ∃ (N : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))) (_ : N.Normal),
      N = secCyc (CoreAssembly.conjClass (tightCore Rd)) (z * t) (z * t) ∧
      LieModel ((SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t) ⧸ N) ⧸
        Subgroup.center (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t) ⧸ N))
        .PSL 4 3 1 ∧
      LieModel ↥((sigmaFixGen (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t)
          (tightCore Rd)) σ).map ((QuotientGroup.mk' (Subgroup.center
            (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t) ⧸ N))).comp
          (QuotientGroup.mk' N))) .PSL 3 3 1 ∧
      ¬ ∃ w : SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t), ∀ x, σ x = w * x * w⁻¹ := by
  obtain ⟨N, hNn, hNeq, hcent⟩ := hs.exists_centOmega3_of_E4 h4 hE hcj hω
  have hNk : N = Subgroup.zpowers (k * k') := hNeq.trans hkk
  have hr := hRk _ _ _ _ _ _ hσ.toTwinBase3 (hs.noThreeOver2_secFam hE) N hNk hcent
  obtain ⟨hpsl, hL3, hout⟩ := h1521 _ _ _ _ _ _ σ hσ N hNk hr
  exact ⟨N, hNn, hNeq, hpsl, hL3, hout⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
