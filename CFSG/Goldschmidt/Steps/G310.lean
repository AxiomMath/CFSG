module

public import CFSG.Goldschmidt.Steps.G310Bar
public import CFSG.Goldschmidt.Steps.G310Core2

public section

namespace CFSG.Goldschmidt

open CFSG.Open

theorem G310.typeIILayer_eq {G : Type} [Group G] (H A : Subgroup G) :
    typeIILayer H A = preOf H (G310.layerII (barOf H A)) := by
  rw [typeIILayer, G310.layerII, G310.typeIISet, G310.barOf_normalClosureIn]

theorem G310 :
    ∀ (G : Type) [Group G] [Finite G] (H A : Subgroup G), IsSStarIn H A → ∀ p : ℕ, p.Prime →
      p ≠ 2 → ∀ P : Subgroup G, Maximal (· ∈ sigN H A p) P →
      fusionIsSylowIn p (P ⊓ oddCoreOf H) (oddCoreOf H) ∧
        typeIILayer H A ⊔ H ⊓ Subgroup.normalizer (P : Set G) = H := by
  intro G _ _ H A hS p hp hp2 P hP
  have hA : IsPGroup 2 A := G310.isPGroup_two_of_isSStarIn hS
  refine ⟨(G310.fusionIsSylowIn_of_maximal_sigN hS.1 hA hp hp2 hP).2, ?_⟩
  have hO := goldschmidtOddCore_quotient_eq_bot H
  have hS' := SStarTransport.isSStarIn_barOf hS
  have hP' := G310.maximal_sigN_barOf hS.1 hA hp hp2 hP
  have hcore := G310.top_le_layerII_sup_normalizer hO hS' hp hp2 hP'
  have := G310.layerII_normal (barOf H A)
  rw [G310.typeIILayer_eq]
  exact G310.le_preOf_sup_normalizer hS.1 hA hp hp2 hP hcore

end CFSG.Goldschmidt
