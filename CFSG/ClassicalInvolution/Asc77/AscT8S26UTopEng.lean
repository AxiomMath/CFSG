module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm8
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Top

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}

theorem s26_top_notMem_ofE (hJ : J ∈ omegaNbr Ω K)
    (hne : omegaNbrGen Ω K ≠ J ⊔ oddCoreOf (omegaNbrGen Ω K))
    (hmap : ∀ {L' J' : Subgroup ↥(omegaNbrGen Ω K)},
      L' ∈ restrictFamily Ω (omegaNbrGen Ω K) → J' ∈ restrictFamily Ω (omegaNbrGen Ω K) →
      L'.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(omegaNbrGen Ω K))) = ⊤ →
      J'.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(omegaNbrGen Ω K))) = ⊤) :
    (⊤ : Subgroup (↥(omegaNbrGen Ω K) ⧸ classicalInvolutionOddCore ↥(omegaNbrGen Ω K))) ∉
      oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K)) := by
  intro htopΦ
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hJ
  obtain ⟨L', hL', hL'top⟩ := htopΦ
  have hJ' : J.subgroupOf X ∈ restrictFamily Ω X := ⟨J, hJ.1, hJX, rfl⟩
  have hJtop := hmap hL' hJ' hL'top
  apply hne
  refine le_antisymm ?_ (sup_le hJX (oddCoreOf_le_self X))
  intro x hx
  have hxtop : (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ⟨x, hx⟩ ∈
      (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) := by
    rw [hJtop]
    trivial
  obtain ⟨j', hj', hj'x⟩ := Subgroup.mem_map.mp hxtop
  have hn : j'⁻¹ * ⟨x, hx⟩ ∈ classicalInvolutionOddCore ↥X := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hj'x
    exact hj'x
  have hnG : ((j'⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ oddCoreOf X :=
    Subgroup.mem_map_of_mem X.subtype hn
  have hjJ : (j' : G) ∈ J := Subgroup.mem_subgroupOf.mp hj'
  have hx' : x = (j' : G) * ((j'⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by
    simp
  rw [hx']
  exact Subgroup.mul_mem_sup hjJ hnG

end Top

end CFSG.ClassicalInvolution.Asc77
