module

public import CFSG.Quasithin.H13.L32NStatements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Thm14326One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    (centerOf (fsuU T V) = fsuV1 T V ∧ CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) ∨
      Nonempty (G ≃* NativeSporadic.HS)

@[expose] def Thm1443One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
      LieModel G .G2 0 3 1

@[expose] def Thm144Big_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5

theorem stmt14_4_14_of_inputs_F4 (h14326 : Thm14326One_F4) (h1443 : Thm1443One_F4) (h144 : Thm144Big_F4) :
    Stmt14_4_14_F4 := by
  intro G _ _ T L V hyp hF hU
  have h : Hyp14310One G T L V := ⟨hyp, hF, hU⟩
  rcases h14326 G T L V h with ⟨-, hext⟩ | hHS
  · exact Or.inr (h1443 G T L V h hext (h144 G T L V h hext))
  · exact Or.inl hHS

end CFSG.Quasithin.H13
