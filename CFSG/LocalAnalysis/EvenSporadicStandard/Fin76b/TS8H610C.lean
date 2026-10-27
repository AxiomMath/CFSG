module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H610A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem Oz_sub_X {α : G} (hα : AlphaSpec S z t α) {u : G}
    (hu : u ∈ {u : G | ∃ f ∈ Fsub h hα, u = f * z * f⁻¹}) : u ∈ XSet S E z := by
  obtain ⟨f, hf, rfl⟩ := hu
  exact h.X_inv hf.1 h.z_mem_X

theorem alpha_orbit_F {α : G} (hα : AlphaSpec S z t α) :
    {u : G | ∃ f ∈ Fsub h hα, u = f * α * f⁻¹} = {α, α * t} := by
  ext u
  constructor
  · rintro ⟨f, hf, rfl⟩
    rcases h.alpha_orbit hα hf.1 with h1 | h1
    · left; exact h1
    · right; exact h1
  · rintro (rfl | rfl)
    · exact ⟨1, one_mem _, by group⟩
    · refine ⟨z, h.U_le_Fsub hα (mem_sup_left h.zS), ?_⟩
      exact (h.z_conj_alpha hα).symm

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
