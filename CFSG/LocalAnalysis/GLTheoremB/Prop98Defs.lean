module

public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
public import CFSG.LocalAnalysis.GLTheoremB.UniqStatements

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

@[expose] def Lemma99 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M →
      ∀ D : Subgroup G, D ≤ B → IsPPlane p D →
        ∀ L : Subgroup G, GLAPComponent p M L →
          ¬ barX p M (gammaD D) ≤
            Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
              Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
          ∃ (D₀ : Set G) (K : G → Subgroup G),
            (∀ d ∈ D₀, d ∈ D ∧ d ≠ 1) ∧
            (∀ d ∈ D₀,
              GLAPComponent p (piLayer p (L ⊓ Subgroup.centralizer ({d} : Set G))) (K d) ∧
                (B ≤ Subgroup.normalizer (K d : Set G) ∧
                  barX p M (gammaD D) ≤
                    Subgroup.normalizer ((barX p M (K d) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
                      Set (↥M ⧸ GLAPPrimeCore p ↥M))) ∧
                ¬ barX p M (gammaD D) ≤
                  Subgroup.centralizer ((barX p M (K d) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
                    Set (↥M ⧸ GLAPPrimeCore p ↥M)) ∧
                K d ≤ piOf p d ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))) ∧
            barX p M L = ⨆ d ∈ D₀, barX p M (K d)

@[expose] def Lemma911 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M → p = 3 →
      ∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
        IsTwoPrimeComp (alphaOf p M ⊓ Subgroup.centralizer ({b} : Set G)) J →
          IsTwoPrimeComp (Subgroup.centralizer ({b} : Set G)) J

@[expose] def Input22_5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → GLAPPrimeCore p X = ⊥ →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      ∀ B : Subgroup X, IsElemAbelian p B →
        pRank p (⊤ : Subgroup (MulAut ↥K)) < pRank p B →
        ∀ k : ℕ, 1 ≤ k → k + pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ pRank p B →
          K ≤ GLBCore p k B

@[expose] def InputPiGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → IsPiGroup p ↥K →
      ∀ B : Subgroup X, IsElemAbelian p B → GLATwoLocalRank p X ≤ pRank p B →
        K ≤ GLBCore p (pRank p B - 1) B

end CFSG.LocalAnalysis.GLTheoremB
