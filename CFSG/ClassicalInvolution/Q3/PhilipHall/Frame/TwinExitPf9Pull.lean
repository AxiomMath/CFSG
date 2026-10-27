module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt

section Pull

variable {Y : Type} [Group Y] [Finite Y]


variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem LiftedAtSec.liftedAt (hd : Q8TwinDatum R S t) {c : Y}
    {htc : t ∈ Subgroup.centralizer ({c} : Set Y)} (h : LiftedAtSec R c t htc) :
    LiftedAt R c t := by
  classical
  obtain ⟨ht', L, hLle, hL⟩ := h
  have hidem := tightCore_idem (secR R c)
  rw [hidem] at hLle
  set H := subnormalClosure (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
    with hH
  set Kc : Subgroup ↥(Subgroup.centralizer ({c} : Set Y)) :=
    tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) with hKc
  have hKcH : Kc ≤ H := le_subnormalClosure _
  set A : Subgroup ↥H := Kc.subgroupOf H with hAdef
  have hAt : A ≤ Subgroup.centralizer ({(⟨⟨t, htc⟩, ht'⟩ : ↥H)} : Set ↥H) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have haK : (a : ↥(Subgroup.centralizer ({c} : Set Y))) ∈ Kc := ha
    have haR : ((a : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) ∈ R :=
      Subgroup.mem_subgroupOf.mp (tightCore_le _ haK)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hd.cent haR)
    apply Subtype.ext
    apply Subtype.ext
    exact this
  have hAL : A.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)) ≤ L := by
    refine le_trans ?_ hLle
    have h1 : tightCore ((R.subgroupOf (Subgroup.centralizer ({c} : Set Y))).subgroupOf H) =
        A := CFSG.ClassicalInvolution.Q3.tightCore_subgroupOf hKcH
    rw [← h1]
    exact map_tightCore_le _ _
  obtain ⟨K, hK, hAK⟩ := exists_sectionMember_of_oddQuot' (isSubnormal_subnormalClosure _) ht'
    (Subtype.ext (TwinEdge.t_mul_t hd)) hL hAt hAL
  refine ⟨K, hK, ?_⟩
  have h2 : A.map H.subtype = Kc := Subgroup.map_subgroupOf_eq_of_le hKcH
  rw [h2] at hAK
  exact hAK

end Pull

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
