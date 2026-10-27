module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieBase
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.Ree.LargeReeInvolution
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem tabIdentFor_twistedF4
    : TabIdentFor @Ident.FamTwistedF4 := by
  intro G _ _ X K t hs hX
  obtain ⟨hsimple, f, hodd, hf3, hmodel⟩ := hX
  exfalso
  obtain ⟨-, -, -, -, -, hinner, hiso⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions ↥X 2 f hmodel
  obtain ⟨-, a, hfa, hmodel'⟩ := hmodel
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hmodel'
  have : Fintype F := Fintype.ofFinite F
  have : CharP F F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hF]
    rfl)
  obtain ⟨⟨E⟩, -⟩ := hiso a F hfa hF ⟨e₀⟩
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := hfa ▸ hF
  have ha : 1 ≤ a := by omega
  have hα : (hs.conjAut : MulAut ↥X) ∈ inner ↥X := by
    refine hinner _ ?_
    rw [pow_two]
    exact MulEquiv.ext fun y => hs.conjAut_conjAut y
  obtain ⟨x, hx⟩ := hs.exists_inner_of_mem_inner hα
  exact hs.false_of_inner hsimple E
    (fun y hy B => (large_Ree_involution_centralizers_component_free a ha F hF').1 y hy B) x hx

end CFSG.QuasithinUnique.Id2519
