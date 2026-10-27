module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1P1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Stab
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SCore

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_K_inf_Y (c : Ctx7 G L) (hH : F33Hyp c.s c.e) : y7aK c ⊓ y7aY c = C1 c.e := by
  have h := c.y7acfg hH
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxK, hxY⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨-, -, hxcom⟩ := hxK
    have hxA : x ∈ normalizer (c.s.fr.A : Set G) := s5_Y_le_NA c.toCtx5 hH hxY
    refine y6_K_core c.toCtx5 hH hxY ?_
    intro a haA
    have haC1 : a ∈ C1 c.e := Subgroup.mem_sup_left haA
    have haxV : ⁅a, x⁆ ∈ V1 c.e := hxcom a haC1
    have haxA : ⁅a, x⁆ ∈ c.s.fr.A := by
      have hxga : x * a * x⁻¹ ∈ c.s.fr.A := (Subgroup.mem_normalizer_iff.mp hxA a).mp haA
      have hmul : a * (x * a * x⁻¹)⁻¹ ∈ c.s.fr.A :=
        Subgroup.mul_mem _ haA (Subgroup.inv_mem _ hxga)
      simpa only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc] using hmul
    have hmem : ⁅a, x⁆ ∈ c.s.fr.A ⊓ V1 c.e := Subgroup.mem_inf.mpr ⟨haxA, haxV⟩
    rwa [y7a_A_inf_V h] at hmem
  · exact le_inf (y7a_C1_le_K h) (y6_C1_le_NAt h.cfg)

theorem y7a_K_eq_C1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) : y7aK c = C1 c.e := by
  have hKY : y7aK c ≤ y7aY c := by
    rw [← y7a_normC0_eq c hH]
    exact y7a_K_le_NC0 (c.y7acfg hH)
  rw [← y7a_K_inf_Y c hH]
  exact (inf_eq_left.mpr hKY).symm

theorem y7a_K_le_X (c : Ctx7 G L) : y7aK c ≤ y7aX c :=
  fun _ hx => Subgroup.mem_inf.mpr ⟨hx.1, hx.2.1⟩

end CFSG.OddStandard.HigherRank.YamadaG23
