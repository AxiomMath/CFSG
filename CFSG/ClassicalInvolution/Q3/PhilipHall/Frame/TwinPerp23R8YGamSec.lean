module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamSyl
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bCover
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf7Distinct
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf25Bridge
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf22AE5Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Mod
open CFSG.ClassicalInvolution.Q3.TC.Thin

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem section_gen (hc : P23Cfg n Y R S t K' W u e g) (hAE : SecAE R u 5) :
    ∃ (x vH : ↥(coreHull (Om R) u)) (v' : Y), hcoeHom (Om R) u x = u * e ∧ x * x = 1 ∧
      hcoeHom (Om R) u vH = v' ∧ (t = v' ∨ t = u * v') ∧ vH * vH = 1 ∧
      Subgroup.centralizer ({(QuotientGroup.mk x :
          ↥(coreHull (Om R) u) ⧸ classicalInvolutionOddCore ↥(coreHull (Om R) u))} :
        Set (↥(coreHull (Om R) u) ⧸ classicalInvolutionOddCore ↥(coreHull (Om R) u))) ⊔
        Subgroup.centralizer ({(QuotientGroup.mk vH :
          ↥(coreHull (Om R) u) ⧸ classicalInvolutionOddCore ↥(coreHull (Om R) u))} :
        Set (↥(coreHull (Om R) u) ⧸ classicalInvolutionOddCore ↥(coreHull (Om R) u))) = ⊤ := by
  classical
  obtain ⟨J₁, J₂, x, κ₁, κ₂, vH, v', hJ₁, hJ₂, hne₂, hτ₁, hτ₂, hvx, hxx, hκ₁W, hκ₂W, hκ₁sq, hκ₂sq,
    hκ₁₂, hκ₁m, hκ₂m, hU₁, hU₂, hvH, hzv, hvHform, hvH2, hvHx, hvH1, hvHx1⟩ := frame_at_u hc
  obtain ⟨I⟩ := hAE
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) u) with hN
  have hS := TwinPerpV3.layer_q8Section hc.std.perp hd.hu2
  have hK₁ := secImg_mem_secFam hJ₁
  have hK₂ := secImg_mem_secFam hJ₂
  have hne : secImg (Om R) u J₂ ≠ secImg (Om R) u J₁ :=
    TwinPerpV3.secImg_ne_of_twin hΩ hc2 hJ₂ hJ₁ hne₂ hτ₂ hτ₁
  have hker : I.φ.ker = ⊥ := TwinThmEW.Ae5Q8.ae5_ker_bot hS I hK₁ hK₂ hne hU₁ hU₂
  have hH : TL4.AECoverHyp I :=
    TwinPerpV3.A6b.aeCoverHyp_of_twins (by norm_num) (by norm_num) hS I hK₁ hK₂ hne hU₁ hU₂
  have F := TwinDisc.AE5.q8Fam_of_aeIdent_n (le_refl 5) hS I
  set ψ : (↥(coreHull (Om R) u) ⧸ N) →* AEQ 5 := TwinThmEW.psiOfF F I with hψdef
  have hinjφ : Function.Injective I.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hψinj : Function.Injective ψ := fun a b hab => congrArg Subtype.val (hinjφ hab)
  obtain ⟨p, b₁, hKl₁⟩ := TwinThmEW.psi_label F I hK₁
  obtain ⟨p', b₂, hKl₂⟩ := TwinThmEW.psi_label F I hK₂
  have hψx : ψ (QuotientGroup.mk' N x) = AE.zBar (miss p) (card_miss p) :=
    TwinThmEW.psi_zimg F I hK₁ hKl₁ hU₁
  have hψx' : ψ (QuotientGroup.mk' N x) = AE.zBar (miss p') (card_miss p') :=
    TwinThmEW.psi_zimg F I hK₂ hKl₂ hU₂
  obtain rfl : p = p' := (miss_inj (AE.eq_of_zBar_eq (by norm_num) (hψx'.symm.trans hψx))).symm
  have hψκ₁ : ψ (QuotientGroup.mk' N κ₁) ∈ AE.memBar (miss p) (card_miss p) b₁ := by
    rw [← hKl₁]; exact Subgroup.mem_map_of_mem _ hκ₁m
  have hψκ₂ : ψ (QuotientGroup.mk' N κ₂) ∈ AE.memBar (miss p) (card_miss p) b₂ := by
    rw [← hKl₂]; exact Subgroup.mem_map_of_mem _ hκ₂m
  have hψκ₁sq : ψ (QuotientGroup.mk' N κ₁ * QuotientGroup.mk' N κ₁) =
      AE.zBar (miss p) (card_miss p) := by
    rw [← map_mul, hκ₁sq]; exact hψx
  have hψκ₂sq : ψ (QuotientGroup.mk' N κ₂ * QuotientGroup.mk' N κ₂) =
      AE.zBar (miss p) (card_miss p) := by
    rw [← map_mul, hκ₂sq]; exact hψx
  have hκ₁₂' : QuotientGroup.mk' N κ₁ * QuotientGroup.mk' N κ₂ =
      QuotientGroup.mk' N κ₂ * QuotientGroup.mk' N κ₁ := by
    rw [← map_mul, ← map_mul, hκ₁₂]
  obtain ⟨T, hT, -, hTN⟩ := exists_sylow_normW hc hd.huW
  have hmap := TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2 h2
  have hLC : rLayer (Om R) u ≤ Subgroup.centralizer ({u} : Set Y) := rLayer_le_centralizer _ _
  have hnL : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer (rLayer (Om R) u : Set Y) :=
    fun c hcc => mem_normalizer_iff_conjSub_eq.mpr (conjSub_rLayer_eq hΩ hcc)
  set e₀ : ↥(coreHull (Om R) u) ≃* ↥(rLayer (Om R) u) := TwinPerpV3.hullEquiv hmap with he₀
  let ψL : ↥(rLayer (Om R) u) →* AEQ 5 :=
    ψ.comp ((QuotientGroup.mk' N).comp e₀.symm.toMonoidHom)
  have hvec : ∀ i : Fin 4, ∃ h : ↥(coreHull (Om R) u), hcoeHom (Om R) u h ∈ T ∧
      ψ (QuotientGroup.mk' N h) = mkQ 5 (vpair p (emb (miss p) (card_miss p) i)) := by
    intro i
    set s := emb (miss p) (card_miss p) i with hs
    have hsp : p ≠ s := by
      have hmem : s ∈ Set.range (emb (miss p) (card_miss p)) := ⟨i, rfl⟩
      rw [range_emb] at hmem
      intro h
      rw [← h] at hmem
      simp [miss] at hmem
    have hv : vpair p s ∈ evenVec 5 := vpair_mem_evenVec hsp
    have hvae : vpair p s ∈ aeSub 5 :=
      ⟨((mem_evenVec).mp hv).2, by rw [((mem_evenVec).mp hv).1]; simp⟩
    have hvr : mkQ 5 (vpair p s) ∈ ψL.range := by
      have h1 : mkQ 5 (vpair p s) ∈ I.φ.range := by
        rw [I.range_eq]; exact Subgroup.mem_map_of_mem _ hvae
      obtain ⟨z, hz⟩ := h1
      obtain ⟨hh, hhz⟩ := QuotientGroup.mk_surjective (z.1 : ↥(coreHull (Om R) u) ⧸ N)
      refine ⟨e₀ hh, ?_⟩
      show ψ (QuotientGroup.mk' N (e₀.symm (e₀ hh))) = _
      rw [MulEquiv.symm_apply_apply]
      have hψz : ψ z.1 = I.φ z := rfl
      show ψ (QuotientGroup.mk hh) = _
      rw [hhz, hψz]
      exact hz
    obtain ⟨s', hsT, hsψ⟩ := exists_mem_inf_of_evenVec hT hLC hnL ψL hv hvr
    refine ⟨e₀.symm s', ?_, hsψ⟩
    have hcoe := TwinPerpV3.hullEquiv_coe hmap (e₀.symm s')
    rw [MulEquiv.apply_symm_apply] at hcoe
    show ((e₀.symm s' : ↥(coreHull (Om R) u)) : ↥(Subgroup.centralizer ({u} : Set Y))).1 ∈ T
    rw [← hcoe]
    exact hsT
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have hconj : ∀ i : Fin 4, ∃ s : ↥(coreHull (Om R) u) ⧸ N,
      ψ s = mkQ 5 (vpair p (emb (miss p) (card_miss p) i)) ∧
      (s * QuotientGroup.mk' N κ₁ * s⁻¹) * QuotientGroup.mk' N κ₂ =
        QuotientGroup.mk' N κ₂ * (s * QuotientGroup.mk' N κ₁ * s⁻¹) := by
    intro i
    obtain ⟨h, hTh, hψh⟩ := hvec i
    refine ⟨QuotientGroup.mk' N h, hψh, ?_⟩
    have hkey : (h * κ₁ * h⁻¹) * κ₂ = κ₂ * (h * κ₁ * h⁻¹) := by
      apply hcoeHom_injective (Om R) u
      simp only [map_mul, map_inv]
      have hH₀ : hcoeHom (Om R) u h ∈ Subgroup.normalizer (W : Set Y) := hTN hTh
      have hk₁ := (Subgroup.mem_normalizer_iff.mp hH₀ (hcoeHom (Om R) u κ₁)).mp hκ₁W
      exact hWab _ hk₁ _ hκ₂W
    have := congrArg (QuotientGroup.mk' N) hkey
    simpa only [map_mul, map_inv] using this
  obtain ⟨a₁, a₂, hs₁, hs₂, ha₁ψ, ha₂ψ, ha₁ae, ha₂ae, hp₁₂, hp₁₂'⟩ :=
    vec_of_conj_comm ψ hψκ₁ hψκ₂ hψκ₁sq hψκ₂sq hκ₁₂' hconj
  set ι₀ := emb (miss p) (card_miss p) with hι₀
  obtain ⟨k, hk, k', hk', hkk', a, haS, hap, haae, hψa⟩ : ∃ k ∈ secImg (Om R) u J₁,
      ∃ k' ∈ secImg (Om R) u J₂, QuotientGroup.mk' N vH = k * k' ∧
        ∃ a : Wr 5, SupportedOn a (Set.range ι₀) ∧ a.perm = 1 ∧ a ∈ aeSub 5 ∧ ψ (k * k') = mkQ 5 a := by
    rcases hvHform with hv | hv
    · refine ⟨QuotientGroup.mk' N κ₁, hκ₁m, QuotientGroup.mk' N κ₂, hκ₂m, by rw [hv, map_mul],
        a₁ * a₂, hs₁.mul hs₂, hp₁₂, (aeSub 5).mul_mem ha₁ae ha₂ae, ?_⟩
      rw [map_mul, ha₁ψ, ha₂ψ, map_mul]
    · refine ⟨(QuotientGroup.mk' N κ₁)⁻¹, Subgroup.inv_mem _ hκ₁m, QuotientGroup.mk' N κ₂, hκ₂m,
        by rw [hv, map_mul, map_inv], a₁⁻¹ * a₂, hs₁.inv.mul hs₂, hp₁₂',
        (aeSub 5).mul_mem ((aeSub 5).inv_mem ha₁ae) ha₂ae, ?_⟩
      rw [map_mul, map_inv, ha₁ψ, ha₂ψ, map_mul, map_inv]
  have hψvH : ψ (QuotientGroup.mk' N vH) = mkQ 5 a := by rw [hkk']; exact hψa
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull (Om R) u)
  have hvN : QuotientGroup.mk' N vH ≠ 1 := by
    intro h
    have hmem : vH ∈ N := (QuotientGroup.eq_one_iff vH).mp h
    exact hvH1 (Sec13.L94T.eq_one_of_isPGroup_of_odd
      (Sec13.L94T.isPGroup_zpowers_of_mul_self hvH2) hNodd (Subgroup.mem_zpowers vH) hmem)
  have h0 : a ≠ 1 := fun h => hvN (hψinj (by rw [hψvH, h, map_one, map_one]))
  have hz : a ≠ zOf ι₀ := by
    intro h
    have heq : QuotientGroup.mk' N vH = QuotientGroup.mk' N x := by
      apply hψinj
      rw [hψvH, h, hψx]
      rfl
    have hmem : vH * x ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' N (vH * x)) = 1
      rw [map_mul, heq, ← map_mul, hxx, map_one]
    have hsq : (vH * x) * (vH * x) = 1 := by
      calc (vH * x) * (vH * x) = vH * (x * vH) * x := by group
        _ = vH * (vH * x) * x := by rw [hvHx]
        _ = (vH * vH) * (x * x) := by group
        _ = 1 := by rw [hvH2, hxx, one_mul]
    have h1 : vH * x = 1 := Sec13.L94T.eq_one_of_isPGroup_of_odd
      (Sec13.L94T.isPGroup_zpowers_of_mul_self hsq) hNodd (Subgroup.mem_zpowers _) hmem
    apply hvHx1
    calc vH = vH * x * x := by rw [mul_assoc, hxx, mul_one]
      _ = 1 * x := by rw [h1]
      _ = x := one_mul x
  have hpr : ∀ y, y ∈ Set.range ι₀ ↔ y ≠ p := by
    intro y
    rw [hι₀, range_emb]
    simp [miss]
  obtain ⟨ι, hιr, hae⟩ := exists_embed_w0 hpr haS hap haae.1 h0 hz
  have hprod : ψ (k * k') = mkQ 5 (embed ι w0) := by rw [hψa, hae]
  have hιK : ∀ (p'' : Fin 5) (b : Bool), (secImg (Om R) u J₁).map ψ =
      AE.memBar (miss p'') (card_miss p'') b → Set.range ι = ↑(miss p'') := by
    intro p'' b hl
    have hpp : p = p'' := TwinThmEW.psi_point_unique F I hK₁ hKl₁ hl hU₁
    subst hpp
    rw [hιr, hι₀, range_emb]
  have hb : b₁ ≠ b₂ := by
    intro h
    subst h
    exact hne (TwinThmEW.psi_inj F I hK₂ hK₁ (hKl₂.trans hKl₁.symm))
  have hl₁ : ((secImg (Om R) u J₁).subgroupOf (pSpan (TwinDisc.secFam (Om R) u))).map I.φ =
      AE.memBar (miss p) (card_miss p) b₁ := (TwinThmEW.psi_map_eq F I _).symm.trans hKl₁
  have hl₂ : ((secImg (Om R) u J₂).subgroupOf (pSpan (TwinDisc.secFam (Om R) u))).map I.φ =
      AE.memBar (miss p) (card_miss p) b₂ := (TwinThmEW.psi_map_eq F I _).symm.trans hKl₂
  have hcomm : Commutes (secImg (Om R) u J₁) (secImg (Om R) u J₂) := by
    cases b₁ <;> cases b₂
    · exact absurd rfl hb
    · intro x hx y hy
      exact (hH.twin_comm (miss p) (card_miss p) _ hK₂ _ hK₁ hl₂ hl₁ y hy x hx).symm
    · exact hH.twin_comm (miss p) (card_miss p) _ hK₁ _ hK₂ hl₁ hl₂
    · exact absurd rfl hb
  have hgen := TwinThmEW.ae5Gen_of_prod _ _ F I (secImg (Om R) u J₁) hK₁ (secImg (Om R) u J₂) hK₂
    hne (QuotientGroup.mk' N x) hU₁ hU₂ hcomm ι k hk k' hk' hιK hprod
  refine ⟨x, vH, v', hvx, hxx, hvH, hzv, hvH2, ?_⟩
  rw [← hkk'] at hgen
  exact hgen.2.2

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
