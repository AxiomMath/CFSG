module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnFinalFrame
public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Hyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf4Edge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPf

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

set_option linter.unusedSectionVars false

structure TwinConnInputsV₃ (n : ℕ) : Prop where
  uPairSec : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t →
      TwinExitPf9.TwinFrameULiftPairSec (CoreAssembly.conjClass (tightCore R))
  thm4 : Thm4RTwinBelow 3 n

namespace TwinConnV₃

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {n : ℕ}

theorem hyp51_all (hSp : TwinCentRes.ModelFactSp62) (hD4m : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) (hI : TwinConnInputsV₃ n) (h : TwinCoreHyp n Y R S t)
    (hZ : Subgroup.center Y = ⊥)
    (hsolv : ∀ M ∈ CoreAssembly.conjClass (tightCore R), Group.IsSolvable ↥M) :
    ∀ B ∈ TwinFrame.frameSet (CoreAssembly.conjClass (tightCore R)), Hyp51 B := by
  obtain ⟨S₀, h₀⟩ := TwinEdge.twinCoreHyp_core h
  have hid := TwinEdge.tightCore_idem R
  have key : ∀ B ∈ TwinFrame.frameSet (CoreAssembly.conjClass (tightCore (tightCore R))),
      Hyp51 B := by
    intro B hB
    refine TwinExitPf9.hyp51_of_mem_frameSet_new5 hSp hD4m hM12 hI.thm4 h₀ hid hZ
      TL4.d4OddAutInnerNC3_proved ?_ ?_ ?_ hB
    · rw [hid]; exact hsolv
    · rw [hid]; exact hI.uPairSec Y R S t h
    · rw [hid]; exact TwinUActsPf.twinFrameUActs_of_core h
  rwa [hid] at key

theorem autOddFreeOn_of_edges (hSp : TwinCentRes.ModelFactSp62) (hD4m : TwinCentRes.ModelFactD42)
    (hI : TwinConnInputsV₃ n) (h : TwinCoreHyp n Y R S t) (hZ : Subgroup.center Y = ⊥) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M,
      ∀ zM zN : Y, IsUniqueInvolution M zM → IsUniqueInvolution N zN → zM ≠ zN →
        ∀ hcomm : zM ∈ Subgroup.centralizer ({zN} : Set Y),
        ∀ L : Subgroup (OddQuot zN), CFSG.IsComponent L →
          oddQuotMk zN ⟨zM, hcomm⟩ ∈ Subgroup.normalizer (L : Set (OddQuot zN)) →
          (∃ y ∈ L, oddQuotMk zN ⟨zM, hcomm⟩ * y ≠ y * oddQuotMk zN ⟨zM, hcomm⟩) →
          Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk zN ⟨zM, hcomm⟩)) := by
  obtain ⟨S₀, h₀⟩ := TwinEdge.twinCoreHyp_core h
  have hid := TwinEdge.tightCore_idem R
  have := TwinVtx.autOddFreeOn_of_edges_oddFree
    (TwinExitPf4.twinEdgeExitOddFree_proved hSp hD4m n hI.thm4)
    (TwinExitPf4.twinSecAOddFree_proved n) h₀ hid hZ
  rwa [hid] at this

end TwinConnV₃

theorem twinConn_preludeV₃ (hSp : TwinCentRes.ModelFactSp62) (hD4m : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {n : ℕ} (hI : TwinConnInputsV₃ n) (h : TwinCoreHyp n Y R S t)
    (hconn : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))) :
    (∀ K ∈ CoreAssembly.conjClass (tightCore R), ∀ z : Y, IsUniqueInvolution K z →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y)) = ⊥) ∧
      (∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J ∧
        Nonempty (↥J ≃* QuaternionGroup 2)) ∧
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) ∧ TwinGraphStd (tightCore R) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hZ : Subgroup.center Y = ⊥ := InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
  have hΩ := h.hyp
  have htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := iSup_conjClass_eq_top h.gen
  have hz₀ : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core h.datum
  have hsolv : ∀ M ∈ Ω, Group.IsSolvable ↥M := by
    rintro _ ⟨g, rfl⟩
    have hR := Q8Datum.isSolvable h.datum
    have hK : Group.IsSolvable ↥(tightCore R) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (tightCore_le R))
        (Subgroup.inclusion_injective _)
    exact isSolvable_conjSub_of hK g
  have hO : componentClassificationOddCore Y = ⊥ := h.oddFree
  obtain ⟨K', hK', hne'⟩ := h.twin
  have hhyp := TwinConnV₃.hyp51_all hSp hD4m hM12 hI h hZ hsolv
  have hα : ∀ M ∈ Ω, ∀ N ∈ omegaNbr Ω M, ∀ zM zN : Y, IsUniqueInvolution M zM →
      IsUniqueInvolution N zN → zM ≠ zN → alphaOf (Subgroup.closure ({zM, zN} : Set Y)) = ⊥ :=
    fun M hM N hN zM zN hzM hzN hne =>
      TwinFrame.alpha_edge_hyp51 hO hΩ htr hconn hgen hZ hhyp (CoreAssembly.mem_conjClass_self _)
        hK' hne' hM hN hzM hzN hne
  have hθ₀ : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
    obtain ⟨S₀, h₀⟩ := TwinEdge.twinCoreHyp_core h
    have hid := TwinEdge.tightCore_idem R
    exact TwinVtx.oddCent_eq_bot_of_twinCore_oddFree
      (TwinExitPf4.twinEdgeExitOddFree_proved hSp hD4m n hI.thm4)
      (TwinExitPf4.twinSecAOddFree_proved n) h₀ hid hZ (by rw [hid]; exact hconn)
      (by rw [hid]; exact hα)
  have hθ : ∀ K ∈ Ω, ∀ z : Y, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set Y)) = ⊥ := by
    rintro _ ⟨g, rfl⟩ z hz
    have hzg : z = g * t * g⁻¹ := (hz₀.conj g).eq hz |>.symm
    subst hzg
    have hcard := TwinOdd.card_oddCent_conj g t
    rw [hθ₀, Subgroup.card_bot] at hcard
    exact Subgroup.eq_bot_of_card_eq _ hcard
  have hθ' : ∀ K ∈ Ω, ∀ z : Y, IsUniqueInvolution K z →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y)) = ⊥ := by
    intro K hK z hz
    have h1 : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set Y)) = ⊥ := hθ K hK z hz
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  have h2q : IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) h.datum.twoGroup
  have h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J := isPGroup_conjClass_of_oddCent hΩ hz₀ hθ₀ h2q
  have hK₀q8 : Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) := by
    obtain ⟨P, hP, ⟨e⟩⟩ := h.datum.exists_sylow_q8 h.q8
    have hK2 := h2 _ (CoreAssembly.mem_conjClass_self _)
    have hPeq : tightCore R = P := hP.2.2 _ le_rfl hK2 hP.1
    rw [hPeq]
    exact ⟨e⟩
  have hq8 : ∀ J ∈ Ω, Nonempty (↥J ≃* QuaternionGroup 2) := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨e⟩ := hK₀q8
    exact ⟨(Subgroup.equivMapOfInjective (tightCore R) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e⟩
  have hA : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) h.aEmpty
  have hsep : TC.SepHyp Ω :=
    sepHyp_of_thm4RTwin hI.thm4 (le_of_eq h.card) hΩ h2 hq8 hA hZ hθ'
  exact ⟨hθ', fun J hJ => ⟨h2 J hJ, hq8 J hJ⟩, hsep, ⟨hΩ, h2, hsep, h.gen, hconn⟩⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
