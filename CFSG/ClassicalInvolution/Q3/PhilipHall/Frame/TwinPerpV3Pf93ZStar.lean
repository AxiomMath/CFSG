module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf81Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf42Edgeless
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf90AE5MuSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf40Abel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGen

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Sec


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem secNbr_exists_of_perp (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c) (hJ : J ∈ tqMembers3 Ω c)
    (h : secImg Ω c J ∈ omegaNbr (TwinDisc.secFam Ω c) (secImg Ω c K)) :
    ∃ J₀ ∈ tqMembers3 Ω c, J₀ ∈ KPerp Ω K ∧ secImg Ω c J = secImg Ω c J₀ := by
  set N := classicalInvolutionOddCore ↥(coreHull Ω c) with hN
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c)
  have hΛ : HypOmegaGen (hullFam Ω c) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) (coreHull Ω c)
  have hΛ' : HypOmegaGen (TwinDisc.secFam Ω c) := hypOmegaGen_secFam hΩ hc2
  obtain ⟨n, hn, hnb⟩ := CFSG.ClassicalInvolution.Asc77.C25J.exists_conj_omegaNbr_gen
    (Ω := hullFam Ω c) (N := N) hΛ hΛ' hodd
    (TwinThmE.secOf_mem_hullFam hK) (TwinThmE.secOf_mem_hullFam hJ) h
  have h1 := omegaNbr_conj hΛ.conjInvariant hnb n⁻¹
  rw [conjSub_inv_conjSub] at h1
  have h2 : conjSub n⁻¹ (TwinThmE.secOf Ω c J) ∈ KPerp (hullFam Ω c) (TwinThmE.secOf Ω c K) :=
    Set.mem_insert_of_mem _ h1
  obtain ⟨J₀, hJ₀, hJ₀eq, hJ₀perp⟩ := TwinThmE.exists_lift_kPerp hΩ hc2 hK h2
  refine ⟨J₀, hJ₀, hJ₀perp, ?_⟩
  have h5 := congrArg (conjSub n) hJ₀eq
  rw [conjSub_conjSub_inv] at h5
  show (TwinThmE.secOf Ω c J).map (QuotientGroup.mk' N) =
    (TwinThmE.secOf Ω c J₀).map (QuotientGroup.mk' N)
  rw [h5, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
    (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGen

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Balance (oddQuotMk)
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Main


variable {n : ℕ}

theorem v3ZStarSec_proved (hPb : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) : V3ZStarSec n := by
  classical
  intro Y _ _ R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d hμ htC htH hO2
  obtain ⟨W, hW, hconnW⟩ := hμ
  have hC := CoreData.of_S hP.core
  have hPG := hC.partIHypG
  have hΩ := d.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.sq_12
  have hK₃tq := tq_of_hyp22G d
  have hperp3 := kPerp_datum hP d.hK₃.1 d.hzK₃
  have hSig := dstarComp_subset_twinSet_of_conn hPG d.hK₃.1 d.hzK₃ hperp3 hW hconnW
  have hS := layer_q8Section hP d.sq_12
  have hlt := card_layer_lt hP d.mul_ne_one
  have hex : ∀ J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∃ u' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) J) u' := by
    intro J hJ
    obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 _ (secImg_mem_secFam hJ)
    exact ⟨z, hz⟩
  refine mem_zStarOf_of_allMembers hΩ hc2 hK₃tq htC htH ?_
  rcases dichotomy_of_thm4RTwin h4 hlt hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
      (secImg_mem_secFam hK₃tq) with hd | htr
  · exact allMembers_involution_of_connected hΩ hc2 hex hK₃tq d.hzK₃ htC htH hSig hd
  by_cases hconn : T3.DStarConnected (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
  · exact allMembers_involution_of_connected hΩ hc2 hex hK₃tq d.hzK₃ htC htH hSig
      (fun M hM => hconn _ (secImg_mem_secFam hK₃tq) M hM)
  have htrans : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        ∃ g, conjSub g M = N := by
    intro M hM N hN
    obtain ⟨a, ha⟩ := htr M hM
    obtain ⟨b, hb⟩ := htr N hN
    refine ⟨b * a⁻¹, ?_⟩
    rw [← hb, ← ha, ← conjSub_mul]
    congr 1
    group
  set tb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :=
    QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
      (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) with htbdef
  have htb₃ : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) tb :=
    isUniqueInvolution_secImg_mk hK₃tq (hex K₃ hK₃tq) d.hzK₃ htC
  obtain ⟨I⟩ := ExitU.ae5_of_o2 hPb.thmD.d2 hlt hS htrans (secImg_mem_secFam hK₃tq) htb₃
    (by
      obtain ⟨P, hPn, hP2, htP⟩ := hO2
      exact TC.oddCoreImg_centralizer_eq_bot oddCore_quot_eq_bot hPn hP2 htP) hO2 hconn
  have F := AE5.q8Fam_of_aeIdent hS htrans I
  have hgen := F.gen
  obtain ⟨α, hα, b, hlabK⟩ := I.label _ (secImg_mem_secFam hK₃tq)
  obtain ⟨L', hL', hlabL'⟩ := I.label_surj α hα (!b)
  obtain ⟨hne, hcomm⟩ := AE5Mu.twin_comm hS I (secImg_mem_secFam hK₃tq) hL' hlabK hlabL'
  have h2 := AE5.members_twoN (le_refl 5) hS I
  have hnbr : L' ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
      (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) :=
    (TC.mem_omegaNbr_iff hS.hyp h2).mpr ⟨hL', hne.symm, AE5Mu.le_normalizer_of_commutes hcomm⟩
  obtain ⟨J₁, hJ₁tq, rfl⟩ := exists_of_mem_secFam hL'
  obtain ⟨J₀, hJ₀tq, hJ₀perp, hJ₀eq⟩ :=
    TwinLayerGen.secNbr_exists_of_perp hΩ hc2 hK₃tq hJ₁tq hnbr
  rw [hperp3] at hJ₀perp
  have hzJ₀ : IsUniqueInvolution J₀ t := isUniqueInvolution_of_mem_twinSet d.hzK₃ hJ₀perp
  have hK'J₀ : K' ≠ J₀ := fun h =>
    (not_mem_tq_K_of_datum hP d).2 (by rw [h]; exact hJ₀tq)
  have hu₂J₀ : u₂ ∈ trivialOnQuot J₀ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hJ₀tq.1 hK'J₀ d.hzK' hzJ₀ d.hu₂.1
  have t23 : u₂ ∈ trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 d.hK₃.1 d.hK₃K'.symm d.hzK' d.hzK₃ d.hu₂.1
  have hxC : u₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc u₁ * u₂ * u₂ = (u₂ * u₁) * u₂ := by rw [d.comm₁₂]
      _ = u₂ * (u₁ * u₂) := by group
  have htb₀ : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) J₀) tb :=
    isUniqueInvolution_secImg_mk hJ₀tq (hex J₀ hJ₀tq) hzJ₀ htC
  have hne' : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) J₀ :=
    fun h => hne (h.trans hJ₀eq.symm)
  have hperm : ∀ L ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∃ L' ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        L.map (secAct hΩ hc2 ⟨u₂, hxC⟩).toMonoidHom = L' := by
    intro L hL'
    obtain ⟨J₂, hJ₂, rfl⟩ := exists_of_mem_secFam hL'
    exact ⟨_, secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxC hJ₂),
      secAct_map_secImg hΩ hc2 ⟨u₂, hxC⟩⟩
  have hfx := secAct_fix_secImg hΩ hc2 (F.two _ (secImg_mem_secFam hK₃tq)) hxC t23
  have hfx' := secAct_fix_secImg hΩ hc2 (F.two _ (secImg_mem_secFam hJ₀tq)) hxC hu₂J₀
  have hkey := AE5.psi_dichotomy F I (autOfTop hgen (secAct hΩ hc2 ⟨u₂, hxC⟩))
    (autOfTop_perm hgen _ hperm) (secImg_mem_secFam hK₃tq) (secImg_mem_secFam hJ₀tq) hne'
    htb₃ htb₀ (fun y hy => Subtype.ext (hfx _ hy)) (fun y hy => Subtype.ext (hfx' _ hy))
  have hα2 : secAct hΩ hc2 ⟨u₂, hxC⟩ * secAct hΩ hc2 ⟨u₂, hxC⟩ = 1 := by
    rcases hkey with h1 | h1
    · ext a
      have := congrArg Subtype.val (h1 ⟨a, mem_pSpan_of_top hgen _⟩)
      show (secAct hΩ hc2 ⟨u₂, hxC⟩) ((secAct hΩ hc2 ⟨u₂, hxC⟩) a) = a
      have e : (secAct hΩ hc2 ⟨u₂, hxC⟩) a = a := this
      rw [e, e]
    · ext a
      have e : ∀ b, (secAct hΩ hc2 ⟨u₂, hxC⟩) b = tb * b * tb⁻¹ := fun b =>
        h1 ⟨b, mem_pSpan_of_top hgen _⟩
      show (secAct hΩ hc2 ⟨u₂, hxC⟩) ((secAct hΩ hc2 ⟨u₂, hxC⟩) a) = a
      rw [e, e]
      have hsq := htb₃.sq
      calc tb * (tb * a * tb⁻¹) * tb⁻¹ = (tb * tb) * a * (tb * tb)⁻¹ := by group
        _ = a := by rw [hsq]; group
  have hαα : secAct hΩ hc2 ⟨u₂, hxC⟩ * secAct hΩ hc2 ⟨u₂, hxC⟩ = secAct hΩ hc2 ⟨t, htC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext d.sq₂
  have hcon : ∀ y, y * tb = tb * y := by
    intro y
    have h1 : secAct hΩ hc2 ⟨t, htC⟩ = 1 := hαα ▸ hα2
    rw [secAct_of_mem hΩ hc2 htH] at h1
    have h2 := congrArg (fun f => f y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    have h2' : tb * y * tb⁻¹ = y := h2
    calc y * tb = (tb * y * tb⁻¹) * tb := by rw [h2']
      _ = tb * y := by group
  intro M hM
  obtain ⟨y, rfl⟩ := htrans _ (secImg_mem_secFam hK₃tq) M hM
  have h := htb₃.conj y
  rwa [show y * tb * y⁻¹ = tb by rw [hcon y]; group] at h

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
