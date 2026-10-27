module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SCore

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6_K_inf_Y (c : Ctx6 G L) (hH : F33Hyp c.s c.e) : y6K c ⊓ y6Y c = C1 c.e := by
  have cfg := c.y6cfg hH
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxK, hxY⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨-, -, hxcom⟩ := hxK
    have hxA : x ∈ normalizer (c.s.fr.A : Set G) := s6_Y_le_NA c hH hxY
    refine y6_K_core c.toCtx5 hH hxY ?_
    intro a haA
    have haC1 : a ∈ C1 c.e := by
      rw [y6_C1_eq c]
      exact Subgroup.mem_sup_left haA
    have haxV : ⁅a, x⁆ ∈ V1 c.e := hxcom a haC1
    have haxA : ⁅a, x⁆ ∈ c.s.fr.A := by
      have hxga : x * a * x⁻¹ ∈ c.s.fr.A :=
        (Subgroup.mem_normalizer_iff.mp hxA a).mp haA
      have hmul : a * (x * a * x⁻¹)⁻¹ ∈ c.s.fr.A :=
        Subgroup.mul_mem _ haA (Subgroup.inv_mem _ hxga)
      simpa only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc] using hmul
    have hmem : ⁅a, x⁆ ∈ c.s.fr.A ⊓ V1 c.e := Subgroup.mem_inf.mpr ⟨haxA, haxV⟩
    rwa [y6_A_inf_V cfg] at hmem
  · exact le_inf (y6_C1_le_K cfg) (y6_C1_le_NAt cfg)

end CFSG.OddStandard.HigherRank.YamadaG23
