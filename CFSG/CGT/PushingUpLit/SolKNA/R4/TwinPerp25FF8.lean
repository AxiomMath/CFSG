module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF6
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25SixFam

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 (imgX)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin (TwinT4Hyp)
open scoped commutatorElement

section Final


variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {b : Y} {K : Subgroup Y} {t : Y}

theorem isUniqueInvolution_imgF {r' : ℕ} (hT4 : TwinT4Hyp r' (CentBar b) (famF b K ⊤))
    {J : Subgroup Y} (hJ : imgX b ⊤ J ∈ famF b K ⊤) {w : Y}
    (hw : IsUniqueInvolution (coreAt b J) w) (hwC : w ∈ Subgroup.centralizer ({b} : Set Y)) :
    IsUniqueInvolution (imgX b ⊤ J) (centBarMk b hwC) := by
  obtain ⟨⟨u, hu⟩, -⟩ := hT4.hyp.omega1 _ hJ
  have hwmem : centBarMk b hwC ∈ imgX b ⊤ J :=
    Subgroup.mem_map.mpr ⟨topMk ⟨w, hwC⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hw.mem), rfl⟩
  have hsq : topMk (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) *
      topMk (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) = 1 :=
    Subtype.ext (Subtype.ext hw.sq)
  have hne : topMk (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ≠ 1 := by
    intro h
    have h1 := congrArg (fun t : ↥(⊤ : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) =>
      (((t : ↥(Subgroup.centralizer ({b} : Set Y)))) : Y)) h
    exact hw.ne_one (by simpa using h1)
  have hodd := CFSG.ComponentClassification.OddCore.odd_card (CentTop b)
  have h1 : centBarMk b hwC ≠ 1 := mk_ne_one_of_involution_of_odd hodd hsq hne
  have h2 : centBarMk b hwC * centBarMk b hwC = 1 := by
    rw [← map_mul, hsq, map_one]
  rcases hu.unique _ hwmem h2 with h | h
  · exact absurd h h1
  · rw [h]
    exact hu

end Final

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
