module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma39

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

omit [Finite G] in
theorem conjHom_mul (a b : G) : conjHom (a * b) = (conjHom a).comp (conjHom b) := by
  ext x
  simp only [conjHom_apply, MonoidHom.comp_apply, mul_inv_rev]
  group

end CFSG.EvenSporadicStandard.Solomon78
