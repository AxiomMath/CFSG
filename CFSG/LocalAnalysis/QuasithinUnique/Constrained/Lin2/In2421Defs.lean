module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2421LQ : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    centerOf L = ⊥ → ∀ a ∈ T, a ∉ S → a ^ 2 = 1 →
      (∀ y ∈ lin2Z L (thompsonJ S), a * y = y * a) →
      ∀ g z : G, z ∈ lin2Z L (thompsonJ S) → z ≠ 1 → a = g⁻¹ * z * g → False

@[expose] def Lemma2421B2 : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    centerOf L ≠ ⊥ → n = 2 → ∀ x ∈ T, x ∉ S → ∀ a ∈ T, a ∉ thompsonJ S → a ^ 2 = 1 →
      ∀ g u : G, u ∈ lin2Delta (thompsonJ S) (lin2Z L (thompsonJ S)) x → a = g⁻¹ * u * g → False

end CFSG.QuasithinUnique.Lin2
