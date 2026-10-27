module

public import CFSG.ClassicalInvolution.Q3.Q3T6DHexD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Three.late_hW (d : Std20Three K K' J S R R' W V z t) :
    W = (W ⊓ K) ⊔ (W ⊓ J) := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  have hΩ := d.late_hΩ
  have hΩg := d.late_hΩ
  obtain ⟨η, ⟨S₀, hηS₀, -⟩, hWη⟩ := d.hW
  have hle : (⨆ U ∈ η, U) ≤ (W ⊓ K) ⊔ (W ⊓ J) := by
    refine iSup₂_le fun Y hY => ?_
    have hYU : Y ∈ USet (CoreAssembly.conjClass K) := (hηS₀.1 hY).1
    have hYW : Y ≤ W := by
      rw [hWη]
      exact le_iSup₂ (f := fun U (_ : U ∈ η) => U) Y hY
    obtain ⟨L₁, hL₁, hYL₁⟩ := Sec6Gen.exists_member_of_mem_USet hΩg hYU
    obtain ⟨a, ha⟩ := Sec6Gen.exists_uniqueInvolution hΩg hL₁
    obtain ⟨-, -, -, -, -, -, -, -, hY4⟩ := Sec6Gen.exists_data_of_mem_USet hΩg hYU
    have haY : a ∈ Y := AscL62.mem_of_uniqueInvolution_of_pGroup ha hYL₁
      (Sec6Gen.isPGroup_of_mem_USet hΩg hYU) (by omega)
    obtain ⟨T₁, hT₁D, hT₁L⟩ := Q3CL.Thompson.exists_sylow_mem_DSet hΩ d.hW d.hWS hL₁ hYU hYL₁
      (hYW.trans d.hWS)
    obtain ⟨w₁, s₁, hd₁⟩ := late_exists_dDataGen hΩ d.hW hT₁D hL₁ hT₁L ha
    have hZ := d.late_a_mem_Z hh hL₁ ha (hYW haY) hd₁
    have h1 := hh.line_le hL₁ ha hZ
    have h2 : Y ≤ L₁ ⊓ W := le_inf hYL₁ hYW
    have h3 := h2.trans h1
    rw [hh.W₀_eq, inf_comm K W, inf_comm J W] at h3
    exact h3
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  calc W = ⨆ U ∈ η, U := hWη
    _ ≤ (W ⊓ K) ⊔ (W ⊓ J) := hle

theorem hexAll3 :
    ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
      (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
        Hex20 (CoreAssembly.conjClass K) K J W := by
  intro G _ _ _ K K' J S R R' W V z t d
  exact ⟨d.late_JW, d.late_hW⟩

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
