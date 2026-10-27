module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93Steps
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUMuRest
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22DOpen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf19AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf81Conn
public import CFSG.ClassicalInvolution.Q3.TL3T25
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitU

section Root

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem v3_secRoot {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    ∃ (α : MulAut (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
      (zb : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      α * α * (α * α) = 1 ∧
      (∀ L ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        ∃ L' ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
          L.map α.toMonoidHom = L') ∧
      (∀ a ∈ secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃, α a = a) ∧
      (∀ b ∈ secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄, α b = b) ∧
      IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) zb ∧
      IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) zb ∧
      α * α = MulAut.conj zb := by
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  have hxC : u₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u₂ * (u₁ * u₂) = (u₂ * u₁) * u₂ := by group
      _ = (u₁ * u₂) * u₂ := by rw [← hd.comm₁₂]
  have htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.mul_right (show Commute t u₁ from hd.hz.commute_of_mem hd.hu₁.1)
      (show Commute t u₂ from hd.hzK'.commute_of_mem hd.hu₂.1)).eq
  have htY : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
      coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    mem_coreHull_of_unique hmem hd.hzK₃ htC
  have hx4 : u₂ * u₂ * (u₂ * u₂) = 1 := by rw [hd.sq₂, hd.hz.sq]
  have t23 : u₂ ∈ trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ hd.hK'.1 hd.hK₃.1 hd.hK₃K'.symm hd.hzK' hd.hzK₃ hd.hu₂.1
  have t24 : u₂ ∈ trivialOnQuot K₄ :=
    A7T22.le_trivialOnQuot_of_twin hΩ hd.hK'.1 hF.1.1 hF.2.2.1.symm hd.hzK' hz4 hd.hu₂.1
  refine ⟨secAct hΩ hc2 ⟨u₂, hxC⟩,
    (QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
      LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [← map_mul]
    have : (⟨u₂, hxC⟩ * ⟨u₂, hxC⟩ * (⟨u₂, hxC⟩ * ⟨u₂, hxC⟩) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) = 1 := Subtype.ext hx4
    rw [this, map_one]
  · intro L hL'
    obtain ⟨J₁, hJ₁, rfl⟩ := exists_of_mem_secFam hL'
    exact ⟨_, secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxC hJ₁),
      secAct_map_secImg hΩ hc2 ⟨u₂, hxC⟩⟩
  · exact secAct_fix_secImg hΩ hc2 (secImg_isPGroup' (h2g K₃ hd.hK₃.1)) hxC t23
  · exact secAct_fix_secImg hΩ hc2 (secImg_isPGroup' (h2g K₄ hF.1.1)) hxC t24
  · obtain ⟨htC', htY', h'⟩ := isUniqueInvolution_secImg hΩ hc2 hmem hd.hzK₃
    exact h'
  · obtain ⟨htC', htY', h'⟩ := isUniqueInvolution_secImg hΩ hc2 hmem4 hz4
    exact h'
  · rw [← map_mul]
    have hsq : (⟨u₂, hxC⟩ * ⟨u₂, hxC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) = ⟨t, htC⟩ :=
      Subtype.ext hd.sq₂
    rw [hsq]
    exact secAct_of_mem hΩ hc2 htY

end Root

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
