module

public import CFSG.LieType.SeitzGeneration.HyperIrrBridge
public import CFSG.LieType.SeitzGeneration.HyperLinear

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open

theorem seitzHyperLie_linearNonabIrr : SeitzHyperLie fun d p E₀ => LinearNonabIrr d p E₀ := by
  intro d p hp hp2 hpd hlist E₀ hE hcard hirr
  obtain ⟨n, F, _, _, e, hpF, ⟨x, y, hx, hy, hxy⟩, hirr⟩ := hirr
  have hE' : IsElemAbelian p (E₀.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card (E₀.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  exact hyperGen_top_of_mulEquiv e
    (hyperGen_top_of_irreducible_nonabelian hp hp2 hpF hE' hcard' hx hy hxy hirr)

theorem seitzHyperLieLinearIrr_proof : SeitzHyperLieLinearIrr :=
  seitzHyperLie_linearNonabIrr

theorem seitzHyperLieLinear_unconditional : SeitzHyperLieLinear :=
  seitzHyperLieLinear_of_irr seitzHyperLieLinearIrr_proof

end CFSG.LieType.SeitzGeneration
