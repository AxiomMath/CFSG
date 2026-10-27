module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cTransport
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf25Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.TL3T40
public import CFSG.ClassicalInvolution.Q3.TL3T42
public import CFSG.ClassicalInvolution.Q3.TL3T47
public import CFSG.ClassicalInvolution.Q3.TL3T48
public import CFSG.ClassicalInvolution.Q3.TL3T50
public import CFSG.ClassicalInvolution.Q3.TL3T51
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GCoc
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GSpan
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot mem_trivialOnQuot_iff)

variable {n : ℕ}


@[expose] def PY {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (c : Y) : Set (Subgroup Y) :=
  {J | J ∈ Ω ∧ J ≤ Subgroup.centralizer ({c} : Set Y)}

section Setup

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {c : Y}

theorem mem_tq_of_PY (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) {J : Subgroup Y}
    (hJ : J ∈ PY Ω c) : J ∈ tqMembers3 Ω c := by
  have hsyl : IsSylow2In J J := ⟨le_rfl, h2 J hJ.1, fun V' hV' _ hK' => le_antisymm hV' hK'⟩
  exact ⟨hJ.1, TwinADescent3.mem_tq_of_sylCent hΩ (fun M hM => (h2 M hM).to_quotient _) hJ.1
    ⟨J, hsyl, hJ.2⟩⟩

theorem PY_of_tq (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J : Subgroup Y} (hJ : J ∈ tqMembers3 Ω c) : J ∈ PY Ω c := by
  have hcomm : ⁅Subgroup.zpowers c, J⁆ ≤ oddCoreOf J :=
    Subgroup.commutator_le.mpr fun a ha x hx =>
      (mem_trivialOnQuot_iff.mp (Subgroup.zpowers_le.mpr hJ.2 ha)).2 x hx
  obtain ⟨T, hT, hTc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2 hcomm
  have hTJ : J = T := hT.2.2 J le_rfl (h2 J hJ.1) hT.1
  refine ⟨hJ.1, ?_⟩
  rw [hTJ]
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hTc

theorem pSpan_PY (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) : pSpan (PY Ω c) = rLayer Ω c := by
  refine le_antisymm (pSpan_le fun J hJ => A6b.le_rLayer_of_mem hJ.1 (h2 J hJ.1) hJ.2) ?_
  refine iSup₂_le fun R' hR' => iSup_le fun hRc => ?_
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hJR : J = R' := hRJ.2.2 J le_rfl (h2 J hJ) hRJ.1
  subst hJR
  exact le_pSpan ⟨hJ, hRc⟩

end Setup

section Layer

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {c : Y}

theorem mem_secImg_iff (hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥) (J : Subgroup Y)
    (h : ↥(coreHull Ω c)) :
    (QuotientGroup.mk h : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈
        secImg Ω c J ↔ (((h : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) ∈ TwinADescent.coreAt c J := by
  unfold secImg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h', hh', he⟩
    have e : h' = h := by
      have := QuotientGroup.eq.mp (show (QuotientGroup.mk h' : ↥(coreHull Ω c) ⧸
        classicalInvolutionOddCore ↥(coreHull Ω c)) = QuotientGroup.mk h from he)
      rw [hOH, Subgroup.mem_bot, inv_mul_eq_one] at this
      exact this
    subst e
    simpa [Subgroup.mem_subgroupOf] using hh'
  · intro hh
    exact ⟨h, by simpa [Subgroup.mem_subgroupOf] using hh, rfl⟩

@[expose] noncomputable def layerEquiv
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥)
    (hgen : pSpan (TwinDisc.secFam Ω c) = ⊤) :
    ↥(rLayer Ω c) ≃* ↥(pSpan (TwinDisc.secFam Ω c)) :=
  ((TwinPerpV3.hullEquiv hmap).symm.trans
    (MulEquiv.ofBijective (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk']; exact hOH),
        QuotientGroup.mk'_surjective _⟩)).trans
    (((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv).symm)

theorem layerEquiv_val
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥)
    (hgen : pSpan (TwinDisc.secFam Ω c) = ⊤) (y : ↥(rLayer Ω c)) :
    ((layerEquiv hmap hOH hgen y : ↥(pSpan (TwinDisc.secFam Ω c))) : TwinPerpV3.LSec Ω c) =
      QuotientGroup.mk ((TwinPerpV3.hullEquiv hmap).symm y) := rfl

theorem layerEquiv_mem
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥)
    (hgen : pSpan (TwinDisc.secFam Ω c) = ⊤) (J : Subgroup Y) (hJc : TwinADescent.coreAt c J = J)
    (y : ↥(rLayer Ω c)) :
    ((y : Y) ∈ J ↔
      layerEquiv hmap hOH hgen y ∈ (secImg Ω c J).subgroupOf (pSpan (TwinDisc.secFam Ω c))) := by
  rw [Subgroup.mem_subgroupOf, layerEquiv_val, mem_secImg_iff hOH, hJc]
  have := TwinPerpV3.hullEquiv_coe hmap ((TwinPerpV3.hullEquiv hmap).symm y)
  rw [MulEquiv.apply_symm_apply] at this
  rw [← this]

@[expose] noncomputable def layerPsi
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥)
    (hgen : pSpan (TwinDisc.secFam Ω c) = ⊤) (hPS : pSpan (PY Ω c) = rLayer Ω c) :
    ↥(pSpan (PY Ω c)) ≃* ↥(pSpan (TwinDisc.secFam Ω c)) :=
  (MulEquiv.subgroupCongr hPS).trans (layerEquiv hmap hOH hgen)

theorem layerPsi_apply
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥)
    (hgen : pSpan (TwinDisc.secFam Ω c) = ⊤) (hPS : pSpan (PY Ω c) = rLayer Ω c)
    (x : ↥(pSpan (PY Ω c))) :
    layerPsi hmap hOH hgen hPS x = layerEquiv hmap hOH hgen (MulEquiv.subgroupCongr hPS x) :=
  MulEquiv.trans_apply _ _ _

theorem layerPsi_mem
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥)
    (hgen : pSpan (TwinDisc.secFam Ω c) = ⊤) (hPS : pSpan (PY Ω c) = rLayer Ω c) (J : Subgroup Y)
    (hJc : TwinADescent.coreAt c J = J) (x : ↥(pSpan (PY Ω c))) :
    ((x : Y) ∈ J ↔
      layerPsi hmap hOH hgen hPS x ∈ (secImg Ω c J).subgroupOf (pSpan (TwinDisc.secFam Ω c))) := by
  have h1 := layerEquiv_mem hmap hOH hgen J hJc (MulEquiv.subgroupCongr hPS x)
  rw [MulEquiv.subgroupCongr_apply] at h1
  rw [layerPsi_apply]
  exact h1

theorem layerPsi_map
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥)
    (hgen : pSpan (TwinDisc.secFam Ω c) = ⊤) (hPS : pSpan (PY Ω c) = rLayer Ω c) (J : Subgroup Y)
    (hJc : TwinADescent.coreAt c J = J) :
    (J.subgroupOf (pSpan (PY Ω c))).map (layerPsi hmap hOH hgen hPS).toMonoidHom =
      (secImg Ω c J).subgroupOf (pSpan (TwinDisc.secFam Ω c)) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (layerPsi_mem hmap hOH hgen hPS J hJc x).mp (Subgroup.mem_subgroupOf.mp hx)
  · intro hw
    obtain ⟨x, rfl⟩ := (layerPsi hmap hOH hgen hPS).surjective w
    exact ⟨x, Subgroup.mem_subgroupOf.mpr ((layerPsi_mem hmap hOH hgen hPS J hJc x).mpr hw), rfl⟩

theorem nonempty_identY (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hO : oddCoreOf (rLayer Ω c) = ⊥)
    (hgen : pSpan (TwinDisc.secFam Ω c) = ⊤) (I : AEIdent (TwinDisc.secFam Ω c) 6) :
    Nonempty (AEIdent (PY Ω c) 6) := by
  classical
  have hmap := TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2 (fun M hM => (h2 M hM).to_quotient _)
  have hOYu : classicalInvolutionOddCore ↥(rLayer Ω c) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hO
  have hOH : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv (TwinPerpV3.hullEquiv hmap).symm hOYu
  have hPS := pSpan_PY (Ω := Ω) (c := c) h2
  refine ⟨transportIdent (layerPsi hmap hOH hgen hPS) ?_ ?_ I⟩
  · intro L hL
    exact ⟨secImg Ω c L, TwinDisc.secImg_mem_secFam (mem_tq_of_PY hΩ h2 hL),
      layerPsi_map hmap hOH hgen hPS L (A6S.coreAt_eq_self_of_le hL.2 (h2 L hL.1))⟩
  · intro L' hL'
    obtain ⟨J, hJ, rfl⟩ := TwinDisc.exists_of_mem_secFam hL'
    have hJP := PY_of_tq h2 hc2 hJ
    exact ⟨J, hJP, layerPsi_map hmap hOH hgen hPS J (A6S.coreAt_eq_self_of_le hJP.2 (h2 J hJ.1))⟩

end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
