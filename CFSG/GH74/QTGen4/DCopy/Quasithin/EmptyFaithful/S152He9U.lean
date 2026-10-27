module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S152He9Q

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem isUniqueM_YT_F4 (h15206 : StageLemma15206_F4) (h15207 : StageLemma15207_F4) :
    IsUniqueM (yOf152 T Mc M ⊔ T) M := by
  obtain ⟨Y₁, hY₁⟩ := h15206 G T Mc M c.hs
  exact (h15207 G T Mc M c.hs Y₁ hY₁).unique

end Ctx15204

end CFSG.Quasithin.He9
