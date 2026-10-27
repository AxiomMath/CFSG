module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.A15BlockOrbitAux
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.AGLEmbedding

theorem odd_card_center_barM {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) :
    Odd (Nat.card (barM M L ⊓ Subgroup.centralizer
      (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : CFSG.pCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ := pCore_quotient_pCore_eq_bot' 2
  have hK := hL.component.2.1
  exact Nat.coprime_two_left.mp (coprime_card_inf_centralizer_of_pCore_eq_bot hY hK)

end CFSG.AGLEmbeddingD2.McLaughlin

end
