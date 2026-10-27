module

public import CFSG.Quasithin.EmptyFaithful.S152He16D
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He9N

public section

namespace CFSG.Quasithin.He16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Input15204BranchBQuasi_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5)
    (c : Ctx15204 T Mc M H K₁ K₂ π) (Lc : Subgroup G), Tail15204 c Lc →
    yOf152 T Mc M ≤ Lc → ¬ IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc) →
    CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc) → False

theorem input15204BranchB_of_quasi_F4 (h36 : A36ForSQTK)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (hQ : Input15204BranchBQuasi_F4) : Input15204BranchB_F4 := by
  intro G _ _ T Mc M H K₁ K₂ π c Lc tail hYL hnot
  by_cases hq : CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc)
  · exact hQ G T Mc M H K₁ K₂ π c Lc tail hYL hnot hq
  · exact c.false_of_commutator_le tail.le (le_of_mem_cComp tail.comp) tail.sylow
      (commutator_le_of_not_quasisimple h36 h129 c tail hYL hq)

end CFSG.Quasithin.He16
