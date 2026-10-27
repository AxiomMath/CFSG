module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.HardMathSupport.Solomon.LocalBalance.Extremal
public import CFSG.HardMathSupport.Solomon.Coordinator.AlphaEngine

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G] [Finite G]

theorem prop63_of_balance (hSF : SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (hS : GLStanding G 4 3)
    {B : Subgroup G} (hB : IsExtremal B) (h3 : IsBalancedWrt 3 3 B)
    (h2 : IsWeaklyBalancedWrt 3 2 B)
    (hgen : ∀ D₀ : Subgroup G, IsEkIn 3 2 B D₀ → ∀ E' : Subgroup G, IsEkIn 3 3 B E' →
      ⁅GLADelta 3 D₀, E'⁆ ≤ ⨆ (D : Subgroup G) (_ : IsEkIn 3 2 E' D),
        ⁅GLADelta 3 D₀ ⊓ Subgroup.centralizer (D : Set G), E'⁆) :
    ∃ M₀ : Subgroup G, Prop63Out B M₀ := by
  obtain ⟨hB1, -, -, -, -, -, -, -, -, -, E₀, hE₀, heven⟩ := hB
  obtain ⟨hΓ, hO⟩ := glbCore_le_normalizer_alphaE_and_even hSF hbridge hS hB1 h3 h2 hgen hE₀ heven
  exact ⟨Subgroup.normalizer (alphaE 3 2 E₀ : Set G), hΓ, hO⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
