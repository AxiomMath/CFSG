module

public import CFSG.LocalAnalysis.OddStandard.GH71.AhatCent
public import CFSG.LocalAnalysis.OddStandard.GH71.AhatSL25

public section

namespace CFSG.OddStandard.GH71

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData
open scoped commutatorElement

namespace AhatB

theorem specB0 : SpecB0 := by
  intro K _ _ S U hF
  obtain ⟨C, hSP⟩ := exists_frame hF.cover hF.sylow hF.card
  obtain ⟨x, hxS, hx⟩ := exists_lift_mem C hSP d02_mem
  obtain ⟨y, hyS, hy⟩ := exists_lift_mem C hSP d01_mem
  have hxy := Cov.commutator_of_dblI C (by rw [hx]; unfold DblI; decide)
    (by rw [hy]; unfold DblI; decide) (by rw [hx, hy]; unfold DblI; decide)
    (by rw [hx, hy]; decide)
  have hZ : ∀ c ∈ center K, c ∈ ⁅S, S⁆ := fun c hc => by
    by_cases h1 : c = 1
    · rw [h1]
      exact one_mem _
    · rw [Cov.center_eq C hc hxy.1 h1 hxy.2]
      exact commutator_mem_commutator hxS hyS
  obtain ⟨a₁, ha₁S, ha₁⟩ := exists_lift_mem C hSP h01_mem
  obtain ⟨b₁, hb₁S, hb₁⟩ := exists_lift_mem C hSP d02_mem
  obtain ⟨a₂, ha₂S, ha₂⟩ := exists_lift_mem C hSP h45_mem
  obtain ⟨b₂, hb₂S, hb₂⟩ := exists_lift_mem C hSP g2_mem
  have hm : ⁅a₁, b₁⁆ * ⁅a₂, b₂⁆ ∈ ⁅S, S⁆ :=
    mul_mem (commutator_mem_commutator ha₁S hb₁S) (commutator_mem_commutator ha₂S hb₂S)
  have hmρ : C.ρ (⁅a₁, b₁⁆ * ⁅a₂, b₂⁆) = u0 := by
    rw [map_mul, map_commutatorElement, map_commutatorElement, ha₁, hb₁, ha₂, hb₂]
    decide
  intro u hu
  by_cases huz : u ∈ center K
  · exact hZ u huz
  · have hc : (⁅a₁, b₁⁆ * ⁅a₂, b₂⁆)⁻¹ * u ∈ center K := by
      rw [← C.ρ_eq_one_iff, map_mul, map_inv, hmρ, rho_eq_u0 C hSP hF hu huz, inv_mul_cancel]
    have := mul_mem hm (hZ _ hc)
    rwa [mul_inv_cancel_left] at this

theorem specB5 : SpecB5 := by
  intro K _ _ hK N hN
  exact CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple (N := N) hK.1

end AhatB

theorem specB0_holds : SpecB0 := AhatB.specB0

theorem specB1_holds : SpecB1 := AhatB.specB1

theorem specB2_holds : SpecB2 := AhatB.specB2

theorem specB2'_holds : SpecB2' := AhatB.specB2'

theorem specB3_holds : SpecB3 := AhatB.specB3

theorem specB4_holds : SpecB4 := AhatB.specB4

theorem specB5_holds : SpecB5 := AhatB.specB5

theorem ahatSpecAll_holds : AhatSpecAll :=
  ⟨specB0_holds, specB1_holds, specB2_holds, specB2'_holds, specB3_holds, specB4_holds,
    specB5_holds⟩

end CFSG.OddStandard.GH71
