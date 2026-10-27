module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Inputs

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def C61A3Double : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 3 → conjJoin S L ≠ L → C61Concl T H S L

@[expose] def C56DoubleA3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 3 → conjJoin S L ≠ L →
    ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S.relIndex M₀ = 2 → C56_7Concl S H L M₀

@[expose] def C56DoubleNonA3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    ¬ IsAltType L 3 → conjJoin S L ≠ L →
    ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S.relIndex M₀ = 2 → C56_7Concl S H L M₀

theorem c56DoubleCase_of (h3 : C56DoubleA3) (ho : C56DoubleNonA3) : C56DoubleCase := by
  intro G _ _ T M H S L hcs hne M₀ hSM hMT h2
  by_cases hA3 : IsAltType L 3
  · exact h3 G T M H S L hcs hA3 hne M₀ hSM hMT h2
  · exact ho G T M H S L hcs hA3 hne M₀ hSM hMT h2

end CFSG.QuasithinUnique.AppC
