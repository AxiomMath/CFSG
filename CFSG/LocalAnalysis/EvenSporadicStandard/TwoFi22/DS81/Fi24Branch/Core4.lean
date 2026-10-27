module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Extraspecial
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.O2Normalizer

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

structure Core4 (E : Subgroup G) (t z : G) : Prop extends Core3 E t z where
  extra : RExtra t z
  irred : RIrred E t z
  conj : ∃ g : G, g * z * g⁻¹ ∈ Rg t z ∧ g * z * g⁻¹ ≠ z
  o2N : TwoFi22.O2In (normalizer (Rg t z : Set G)) = Rg t z
  N_le_Cz : normalizer (Rg t z : Set G) ≤ Cz z

theorem core4 (c : Core3 E t z) : Core4 E t z :=
  ⟨c, rExtra c, rIrred c, exists_conj_z_mem_R c, O2In_normalizer_R c, normalizer_R_le_Cz c⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
