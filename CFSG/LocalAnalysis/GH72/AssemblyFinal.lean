module

public import CFSG.LocalAnalysis.GH72.AssemblySec3
public import CFSG.LocalAnalysis.GH72.G3bExists

public section

namespace CFSG.GH72

section ClassicalInvolution

theorem hMason_holds :
    ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G,
        Nonempty (↥(P : Subgroup G) ≃* CFSG.CGT.Stroth77.L4Sylow.L4Model n) →
        CFSG.OddStandard.HigherRank.YamadaG23.LitPSLU4S G :=
  hMason_of_exists_productFusion fun 𝔖 => Sec3Setting.exists_productFusion 𝔖

end ClassicalInvolution

end CFSG.GH72
