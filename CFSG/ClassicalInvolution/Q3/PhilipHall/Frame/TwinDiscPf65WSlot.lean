module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf58Shapes
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf64WSlotS
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711Cor
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscThmE
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
public import CFSG.ClassicalInvolution.Q3.TL4TwistTw

public section

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc

theorem mulAut_eq_one_of_fix_members {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (hgen : omegaGen Φ = ⊤) (α : MulAut X) (hfix : ∀ M ∈ Φ, ∀ m ∈ M, α m = m) : α = 1 := by
  have hS : omegaGen Φ ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X) :=
    iSup₂_le fun M hM m hm => hfix M hM m hm
  rw [hgen] at hS
  ext x
  exact hS (Subgroup.mem_top x)


theorem discUZetaTriAt_w (n : ℕ) : DiscUZetaTriAt n shapeW := by
  intro Y _ _ R S t₀ K K' z u J t W s hw hα hne hconn hY htrans h2' hshape hzC htC htY
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have hP : Q3CL.PartIHypG Ω := TwinPerp.partIHypG s.core
  have hK : K ∈ Ω := hf.mem
  obtain ⟨W', hW', ρa, ρb, ρc, w, v, hKa, hKb, hKc, hwK, hvK, hw2, hv2, huv⟩ := hw
  have huW' : u ∈ W' := huv ▸ W'.mul_mem hwK.2 hvK.2
  have hnc : ¬ DbarConnected Ω W' := Q3T6.Mu.thompsonGraphAll hP hK hne hW'
  have n13 : J ∈ omegaNbr Ω K := hf.hJ.2 K (mem_twinSet_self hK hf.hz)
  have hnbr : ρc.K ∈ omegaNbr Ω ρa.K := by rw [hKa, hKc]; exact n13
  have hza : IsUniqueInvolution ρa.K z := by rw [hKa]; exact hf.hz
  have hzc : IsUniqueInvolution ρc.K t := by rw [hKc]; exact hf.ht
  have hcdC := TwinMu.cdSub_le_centralizer_tz hP hW' hnc ρa ρc hnbr hza hzc u
  obtain ⟨V, hVs⟩ := hshape
  have hΦ : HypOmegaGen (secFam Ω u) := hypOmegaGen_secFam hΩ hc2
  have hVmem : V ∈ WSet (secFam Ω u) := by rw [hVs]; exact Set.mem_singleton V
  have hVn : ∀ x, conjSub x V = V := fun x => by
    have h := WSet.conj hΦ.conjInvariant hVmem x
    rw [hVs] at h
    exact h
  have hall := TwinSec711.mem_secD_of_normal hΩ hc2 hW' huW' hVmem hVn
  have htzC : t * z ∈ Subgroup.centralizer ({u} : Set Y) := Subgroup.mul_mem _ htC hzC
  have hfix : ∀ N ∈ secFam Ω u, ∀ a ∈ N, secAct hΩ hc2 ⟨t * z, htzC⟩ a = a := by
    intro N hN
    obtain ⟨J₁, hJ₁, T, hT, hTJ, hTu, rfl⟩ := hall N hN
    have hTtz : T ≤ Subgroup.centralizer ({t * z} : Set Y) :=
      (TwinMu.le_cdSub hT hTu).trans hcdC
    have htq : t * z ∈ trivialOnQuot J₁ :=
      TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁.1 ⟨T, hTJ, hTtz⟩
    exact secAct_fix_secImg hΩ hc2 (h2' _ (secImg_mem_secFam hJ₁)) htzC htq
  have hq8 := q8Section_secFam hΩ hc2 h2 hq hA
  have hone : secAct hΩ hc2 ⟨t * z, htzC⟩ = 1 :=
    mulAut_eq_one_of_fix_members hq8.gen _ hfix
  right
  left
  have hct : secAct hΩ hc2 ⟨t, htC⟩ =
      MulAut.conj (QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull Ω u)) :
        ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) :=
    secAct_of_mem hΩ hc2 htY
  have hmul : secAct hΩ hc2 ⟨t, htC⟩ * secAct hΩ hc2 ⟨z, hzC⟩ = 1 := by
    rw [← map_mul]
    exact hone
  rw [hct] at hmul
  set tb : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u) :=
    QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull Ω u)) with htb
  have htb2 : tb * tb = 1 := by
    rw [htb, ← QuotientGroup.mk_mul]
    have : (⟨⟨t, htC⟩, htY⟩ * ⟨⟨t, htC⟩, htY⟩ : ↥(coreHull Ω u)) = 1 :=
      Subtype.ext (Subtype.ext hf.ht.sq)
    rw [this]
    exact QuotientGroup.mk_one _
  have hcc : MulAut.conj tb * MulAut.conj tb = 1 := by
    rw [← map_mul, htb2, map_one]
  calc secAct hΩ hc2 ⟨z, hzC⟩
      = (MulAut.conj tb)⁻¹ * (MulAut.conj tb * secAct hΩ hc2 ⟨z, hzC⟩) := by group
    _ = (MulAut.conj tb)⁻¹ := by rw [hmul, mul_one]
    _ = MulAut.conj tb := inv_eq_of_mul_eq_one_right hcc

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
