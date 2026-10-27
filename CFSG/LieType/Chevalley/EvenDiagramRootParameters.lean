module

public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem even_diagram_root_parameters
    (t : TwistTag) {K : Type} [Field K] [CharP K 2]
    (σ : K →+* K) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) (c : K) :
    twistHom t K σ (pinnedX t.tag K α c) = pinnedX t.tag K (permLattice t.perm α) (σ c) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσ : Units.map (entrywiseHom σ) (pinnedX t.tag K α c) = pinnedX t.tag K α (σ c) :=
    Units.ext (entrywise_pinnedX σ α (c := c))
  rw [twistHom_apply, hσ, ← twistHom_id_eq, twistHom_id_pinnedX h2 hα]

end CFSG.LieType.Chevalley
