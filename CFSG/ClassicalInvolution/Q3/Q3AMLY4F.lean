module

public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase
public import CFSG.ClassicalInvolution.Q3.Q3AMLY4A

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3AM (nbrLayer exactCore3_le_nbrLayer nbrLayer_le_centralizer
  layerFam)
open scoped commutatorElement

section Top


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem thin_of_top_mem_layerFam (hs : Std8 Ω K J S R T W z t)
    (hT : (⊤ : Subgroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))) ∈
      layerFam Ω K z) :
    nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨L₀, ⟨M, ⟨⟨N, hN, rfl⟩, hMc⟩, hMY, rfl⟩, hQ⟩ := hT
  have hthinN : nbrLayer Ω K z = exactCore3 z N ⊔ oddCoreOf (nbrLayer Ω K z) := by
    apply le_antisymm
    · intro y hy
      have hmem : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)))
          ⟨y, hy⟩ ∈ ((exactCore3 z N).subgroupOf (nbrLayer Ω K z)).map
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))) := by
        rw [hQ]
        trivial
      obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hmem
      have hcN : (c : G) ∈ exactCore3 z N := Subgroup.mem_subgroupOf.mp hc
      have hn : c⁻¹ * ⟨y, hy⟩ ∈ classicalInvolutionOddCore ↥(nbrLayer Ω K z) := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcy
        exact hcy
      have hnG : ((c⁻¹ * ⟨y, hy⟩ : ↥(nbrLayer Ω K z)) : G) ∈ oddCoreOf (nbrLayer Ω K z) :=
        Subgroup.mem_map_of_mem (nbrLayer Ω K z).subtype hn
      have hy' : y = (c : G) * ((c⁻¹ * ⟨y, hy⟩ : ↥(nbrLayer Ω K z)) : G) := by
        simp
      rw [hy']
      exact Subgroup.mul_mem_sup hcN hnG
    · exact sup_le (exactCore3_le_nbrLayer hN) (oddCoreOf_le_self _)
  obtain ⟨y, hyY, hyN⟩ := exists_conj_of_nbr_thin hΩ hs.hz hN hs.hJ hthinN
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z hyY
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hyC
    calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [this]
      _ = z := by group
  have hcore : exactCore3 z J = conjSub y (exactCore3 z N) := by
    have := exactCore3_conjSub y z N
    rwa [hyz, hyN] at this
  have hYn : conjSub y (nbrLayer Ω K z) = nbrLayer Ω K z := conjSub_eq_self_of_mem hyY
  have hOn : conjSub y (oddCoreOf (nbrLayer Ω K z)) = oddCoreOf (nbrLayer Ω K z) := by
    rw [← oddCoreOf_conjSub_eq, hYn]
  calc nbrLayer Ω K z = conjSub y (nbrLayer Ω K z) := hYn.symm
    _ = conjSub y (exactCore3 z N ⊔ oddCoreOf (nbrLayer Ω K z)) := by rw [← hthinN]
    _ = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z) := by
      rw [Asc77.conjSub_sup, hOn, hcore]

end Top

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4
