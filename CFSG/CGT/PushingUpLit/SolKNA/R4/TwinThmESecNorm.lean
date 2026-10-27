module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf7Norm
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

namespace ThmE

section Norm


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H Y : Subgroup G}

theorem MinCex.le_H_of_mem_dstarComp (c : MinCex r Ω K S R W H) {J : Subgroup G}
    (hJ : J ∈ dstarComp Ω K) : J ≤ H := by
  obtain ⟨h, hhH, rfl⟩ := c.hyp.trans J hJ
  intro x hx
  rw [mem_conjSub_iff] at hx
  have := H.mul_mem (H.mul_mem hhH (c.le_H hx)) (H.inv_mem hhH)
  simpa [mul_assoc] using this

theorem MinCex.trans_restrict (c : MinCex r Ω K S R W H) (hKY : K ≤ Y)
    (hall : ∀ J ∈ restrictFamily Ω Y, ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = J) :
    ∀ J ∈ dstarComp (restrictFamily Ω Y) (K.subgroupOf Y),
      ∃ h ∈ H.subgroupOf Y, conjSub h (K.subgroupOf Y) = J := by
  intro J hJ
  have hJΛ : J ∈ restrictFamily Ω Y := by
    rcases dstarComp_subset_insert _ hJ with h | h
    · rw [h]
      exact subgroupOf_mem_restrictFamily c.stand.mem hKY
    · exact h
  obtain ⟨y, rfl⟩ := hall J hJΛ
  refine ⟨y, ?_, rfl⟩
  have h1 := dstarComp_map hJ
  rw [Subgroup.map_subgroupOf_eq_of_le hKY] at h1
  have h2 : (conjSub y (K.subgroupOf Y)).map Y.subtype = conjSub (y : G) K := by
    rw [conjSub_subgroupOf Y y K, Subgroup.map_subgroupOf_eq_of_le]
    have := conjSub_mono (n := (y : G)) hKY
    rwa [conjSub_eq_self_of_mem y.2] at this
  rw [h2] at h1
  exact Subgroup.mem_subgroupOf.mpr ((e18_1 G Ω K S R W H c).1 y h1)

@[expose] def restrictGood (Ω : Set (Subgroup G)) (Y K : Subgroup G) (L : Subgroup ↥Y) : Prop :=
  ∃ J ∈ Ω, J ≤ Y ∧ L = J.subgroupOf Y ∧ J ∈ dstarComp Ω K

theorem restrictGood_step {K : Subgroup G} {L L' : Subgroup ↥Y}
    (hL' : L' ∈ restrictFamily Ω Y) (hgood : restrictGood Ω Y K L)
    (hadj : dstarAdj (restrictFamily Ω Y) L L') : restrictGood Ω Y K L' :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.restrictGood_step hL' hgood hadj

theorem MinCex.restrictGood_le_H (c : MinCex r Ω K S R W H) {L : Subgroup ↥Y}
    (hgood : restrictGood Ω Y K L) : L.map Y.subtype ≤ H := by
  obtain ⟨J, hJ, hJY, rfl, hJK⟩ := hgood
  rw [Subgroup.map_subgroupOf_eq_of_le hJY]
  exact c.le_H_of_mem_dstarComp hJK


end Norm

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
