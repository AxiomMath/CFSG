module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf63E64Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf61AE7Slot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf65WSlot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf60TwinCount
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf44Star
public import CFSG.ClassicalInvolution.Q3.Sec13EndFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

section Proved

open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.TL4

variable {n : ℕ}

theorem discUZetaTriO2_of_shapes' (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (hcit : CIT3Below n)
    (hW : DiscUZetaTriAt n shapeW) (hE64 : DiscUZetaTriAt n shapeE64)
    (hAE7 : DiscUZetaTriAt n (shapeAE 7)) :
    DiscUZetaTriO2 n := by
  intro Y _ _ R S t₀ K K' z u J t W s hw hα hne hconn hY hex hzC htC htY
  have hf := s.data.frame
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have htr : ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ N ∈ CoreAssembly.conjClass (tightCore R),
      ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', hJ'tw, hJ'ne, hJ't, hJ'tq⟩ := exists_twin_mem_tqMembers_u hΩ htr h2 s.data
  have hJtq : J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) u :=
    mem_tqMembers_u_J hΩ htr h2 s.data
  have hlt : Nat.card (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  have hS := q8Section_secFam hΩ hc2 h2 hq hA
  have htrans := TwinMu.Pf3.transY_of_witness h4 s hne hw
  have hodd : ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
      ∀ zb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
        IsUniqueInvolution M zb → oddCoreImg (Subgroup.centralizer ({zb} : Set _)) = ⊥ :=
    fun M hM zb hzb => oddCentEdge_proved n hcit hP _ hlt _ hS htrans (section_edge s) M hM zb hzb
  obtain ⟨M, hM, zb, hzb, hO2⟩ := hex
  have F := ExitU.q8Fam_of_q8Section hS htrans hM hzb (hodd M hM zb hzb) hO2
  have h2' := F.two
  have hD : TC.Thin.ThmDHyp 3 (secFam (CoreAssembly.conjClass (tightCore R)) u) :=
    ⟨F.hyp, F.two, F.card, F.aEmpty, F.gen, F.trans, F.oddFree, F.inO2⟩
  obtain ⟨htC₁, htY₁, htbar⟩ := isUniqueInvolution_secImg hΩ hc2 hJtq hf.ht
  obtain ⟨htC₂, htY₂, htbar'⟩ := isUniqueInvolution_secImg hΩ hc2 hJ'tq hJ't
  have hne' : secImg (CoreAssembly.conjClass (tightCore R)) u J ≠
      secImg (CoreAssembly.conjClass (tightCore R)) u J' :=
    TwinPerpV3.secImg_ne_of_twin hΩ hc2 hJtq hJ'tq hJ'ne.symm hf.ht hJ't
  have hTO : TwinOnlyNbr (secFam (CoreAssembly.conjClass (tightCore R)) u) := by
    obtain ⟨hnb, -⟩ := TwinCount.discUConnSecNbrW n Y R S t₀ K K' z u J t W s hw hne J' hJ'tw hJ'ne hJ'tq
    exact twinOnly_of_trans (hypOmegaGen_secFam hΩ hc2).conjInvariant htrans
      (secImg_mem_secFam hJtq) hnb
  rcases F.thmDConcl hP.thmD.d2 hlt with h1 | ⟨W', hW'⟩ | ⟨E, hE⟩ | I64 | ⟨m, hm5, ⟨I⟩⟩ | I29
  · exfalso
    exact hne' (h1 _ (secImg_mem_secFam hJtq) _ (secImg_mem_secFam hJ'tq))
  · exact hW Y R S t₀ K K' z u J t W s hw hα hne hconn hY htrans h2' ⟨W', hW'⟩ hzC htC htY
  · exfalso
    exact hne' (TC.Thin.eq_of_inv_e8 hD hE (secImg_mem_secFam hJtq) (secImg_mem_secFam hJ'tq)
      htbar htbar')
  · exact hE64 Y R S t₀ K K' z u J t W s hw hα hne hconn hY htrans h2' I64 hzC htC htY
  · by_cases hm7 : m ≤ 7
    · by_cases hm56 : m = 5 ∨ m = 6
      · exact discUZetaTriAt_of_sqTriShape (sqTriShape_ae56 m hm56) Y R S t₀ K K' z u J t W s hw hα hne
          hconn hY htrans h2' ⟨I⟩ hzC htC htY
      · obtain rfl : m = 7 := by omega
        exact hAE7 Y R S t₀ K K' z u J t W s hw hα hne hconn hY htrans h2' ⟨I⟩ hzC htC htY
    · exfalso
      obtain ⟨A, hA, B, hB, C, hC, hBC⟩ :=
        TL4.LinkE2.exists_two_nbrs_of_aeIdent hD (by omega) I
      exact hBC (hTO A hA B hB C hC)
  · exfalso
    obtain ⟨I'⟩ := I29
    obtain ⟨A, hA, B, hB, C, hC, hBC⟩ :=
      TL4.LinkE2.exists_two_nbrs_of_e29 hD I' (secImg_mem_secFam hJtq)
    exact hBC (hTO A hA B hB C hC)

theorem discUZetaTriE4_of_models' (hSp : ExitE4.E4Sp6SqModel) (hO8 : ExitE4.E4O8TwinModel)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n)
    : DiscUZetaTriE4 n := by
  intro Y _ _ R S t₀ K K' z u J t W s hw hα hne hconn hY hO hE hzC htC htY
  have hf := s.data.frame
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have htr : ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ N ∈ CoreAssembly.conjClass (tightCore R),
      ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', hJ'tw, hJ'ne, hJ't, hJ'tq⟩ := exists_twin_mem_tqMembers_u hΩ htr h2 s.data
  have hJtq : J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) u :=
    mem_tqMembers_u_J hΩ htr h2 s.data
  have hlt : Nat.card (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  have hS := q8Section_secFam hΩ hc2 h2 hq hA
  have htrans := TwinMu.Pf3.transY_of_witness h4 s hne hw
  have hodd : ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
      ∀ zb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
        IsUniqueInvolution M zb → oddCoreImg (Subgroup.centralizer ({zb} : Set _)) = ⊥ :=
    fun M hM zb hzb => oddCentEdge_proved n hcit hP _ hlt _ hS htrans (section_edge s) M hM zb hzb
  obtain ⟨htC₁, htY₁, htbar⟩ := isUniqueInvolution_secImg hΩ hc2 hJtq hf.ht
  have h2' : ∀ J₁ ∈ secFam (CoreAssembly.conjClass (tightCore R)) u, IsPGroup 2 ↥J₁ :=
    fun J₁ hJ₁ => (ExitU.members hS htrans (secImg_mem_secFam hJtq) htbar
      (hodd _ (secImg_mem_secFam hJtq) _ htbar) J₁ hJ₁).1
  have hno : ∀ K₁ ∈ secFam (CoreAssembly.conjClass (tightCore R)) u, ∀ zb : ↥(coreHull
      (CoreAssembly.conjClass (tightCore R)) u) ⧸ classicalInvolutionOddCore ↥(coreHull
        (CoreAssembly.conjClass (tightCore R)) u), IsUniqueInvolution K₁ zb → ¬ TightInO2 zb :=
    fun K₁ hK₁ zb hzb hz2 => hO ⟨K₁, hK₁, zb, hzb, hz2⟩
  have hTO : TwinOnlyNbr (secFam (CoreAssembly.conjClass (tightCore R)) u) := by
    obtain ⟨hnb, -⟩ := TwinCount.discUConnSecNbrW n Y R S t₀ K K' z u J t W s hw hne J' hJ'tw hJ'ne hJ'tq
    exact twinOnly_of_trans (hypOmegaGen_secFam hΩ hc2).conjInvariant htrans
      (secImg_mem_secFam hJtq) hnb
  exact zetaTri_of_sqTri s h2' (ExitE4.sqTriOn_of_twinE4 hSp hO8 hS htrans h2' hno hTO hE) hΩ hc2
    hzC htC htY

theorem discUZetaTriO2_proved (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (hcit : CIT3Below n) : DiscUZetaTriO2 n :=
  discUZetaTriO2_of_shapes' hP h4 hcit (discUZetaTriAt_w n) discUZetaTriAt_e64 discUZetaTriAt_ae7

theorem discUZetaTriE4_proved' (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) : DiscUZetaTriE4 n :=
  discUZetaTriE4_of_models' e4Sp6SqModel_of_certs e4O8TwinModel_of_certs hcit hP h4

theorem discUTzCentT_proved (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n) : DiscUTzCentT n :=
  discUTzCentT_of_branches hcit hP h4 (discUZetaTriO2_proved hP h4 hcit) (discUZetaTriE4_proved' hcit hP h4)

theorem disc14YConnStar_proved (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n) : Disc14YConnStar n :=
  disc14YConnStar_of_tzCent (twinDiscBase_of_thm4 h4) (discUTzCentT_proved hcit hP h4)

theorem twinDiscPerpSPAll_proved : ∀ n, TwinCoreDiscPerpSP n :=
  twinDiscPerpSPAll_of_y14ConnStar (CFSG.ClassicalInvolution.Q3.Sec13.dLeafEnd_three _)
    (fun n hA hP => TwinDisc.disc14YConnStar_proved hA hP (TwinThmEW.t4Supply_of_twoClass n hA hP))

end Proved

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
