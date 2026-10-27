module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Base
public import CFSG.LocalAnalysis.RankThreeUC.GN15Climb

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem GNAbsorbs.of_chief_factor_normalizer (hT : IsSylowTwoOf T ⊤) (h1 : T₁ ≤ omegaOneCenterOf T)
    (h2 : T₂ ≤ baum T) (h2c : (T₂.subgroupOf (baum T)).Characteristic) {A B : Subgroup X}
    (hA : A.Normal) (hB : B.Normal) (hBA : B ≤ A)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A)
    (hAN : A ≤ B ⊔ Subgroup.normalizer (thompsonJ T : Set X))
    (hBabs : GNAbsorbs T T₁ T₂ B) : GNAbsorbs T T₁ T₂ A := by
  rcases cover_of_chief_factor_normalizer hT h1 h2 h2c hA hB hBA hchief hAN with h | h
  · exact GNAbsorbs.of_cover_centralizer hBabs hB h
  · exact GNAbsorbs.of_cover_normalizer hA hB hBabs h

theorem GNAbsorbs.of_le_mul_normalizer_thompsonJ (hT : IsSylowTwoOf T ⊤)
    (h1 : T₁ ≤ omegaOneCenterOf T) (h2 : T₂ ≤ baum T)
    (h2c : (T₂.subgroupOf (baum T)).Characteristic) {H Q : Subgroup X} (hH : H.Normal)
    (hQ : Q.Normal) (hHQ : H ≤ Q) (hQN : Q ≤ H ⊔ Subgroup.normalizer (thompsonJ T : Set X))
    (hHabs : GNAbsorbs T T₁ T₂ H) : GNAbsorbs T T₁ T₂ Q :=
  climb_of_chief_factor_step (P := GNAbsorbs T T₁ T₂)
    (fun _ _ hA hB hBA hchief hAN hBabs =>
      GNAbsorbs.of_chief_factor_normalizer hT h1 h2 h2c hA hB hBA hchief hAN hBabs)
    hH hHabs Q hQ hHQ hQN

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
