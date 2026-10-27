module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S153GExtra

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def L3ULDichotomy_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L →
      ⁅VZ T M, YL153 Yp L⁆ = ⊥ →
      ⁅⁅WL153 T M L, L⁆, YC153 Yp L⁆ = ⊥ ∨
        ∃ y ∈ YC153 Yp L, ∀ u ∈ ⁅WL153 T M L, L⁆, y * u * y⁻¹ = u → u = 1

end CFSG.Quasithin
