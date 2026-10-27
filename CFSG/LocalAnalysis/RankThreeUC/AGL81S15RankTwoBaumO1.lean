module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjSp fieldSp)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)

@[expose] def K541DynkinA2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls →
      ∀ n : ℕ, 2 ≤ n →
        ∀ e : ↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n),
          ∀ s : ↥(Subgroup.normalizer (Ls : Set (X ⧸ gnC T))),
            ∃ (P : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 n))
              (σ : GaloisField 2 n ≃+* GaloisField 2 n),
              MulAut.congr e (Ls.normalizerMonoidHom s) =
                slConjugation 3 (GaloisField 2 n) P * slFieldAut (Fin 3) (GaloisField 2 n) σ

@[expose] def K543DynkinB2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls →
      ∀ n : ℕ, 2 ≤ n →
        ∀ e : ↥Ls ≃* StatedSp 2 (GaloisField 2 n),
          ∀ s : ↥(Subgroup.normalizer (Ls : Set (X ⧸ gnC T))),
            ∃ (A : gsp 2 (GaloisField 2 n)) (σ : GaloisField 2 n ≃+* GaloisField 2 n),
              MulAut.congr e (Ls.normalizerMonoidHom s) =
                conjSp 2 (GaloisField 2 n) A * fieldSp 2 (GaloisField 2 n) σ

end CFSG.LocalAnalysis.RankThreeUC.S15

end
