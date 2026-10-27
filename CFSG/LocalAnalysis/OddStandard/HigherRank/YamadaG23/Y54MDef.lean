module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def IsM3Cand (s : Setting3 G L) (M : Subgroup G) : Prop :=
  s.fr.F ≤ M ∧ M ≤ f4Y s ∧ (∀ n ∈ normIn L s.fr.F, ∀ m ∈ M, n * m * n⁻¹ ∈ M) ∧
    M ⊓ f4X0 s = s.fr.F ∧ M ⊔ f4X0 s = f4Y s

end CFSG.OddStandard.HigherRank.YamadaG23
