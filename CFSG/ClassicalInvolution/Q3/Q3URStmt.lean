module

public import CFSG.ClassicalInvolution.Q3.Q3WShape
public import CFSG.ClassicalInvolution.Phan.Phan3TDefs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Phan (Su)

@[expose] def Phan3Rec : Prop :=
  ∀ {n : ℕ}, 4 ≤ n → ∀ {X : Type} [Group X] {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X},
    Phan.WeakPhanA (GaloisField 3 2) 3 1 n U W →
    Phan.Q3G.AdjacentTripleBlocks (GaloisField 3 2) 3 1 U W →
    ∃ ψ : Su (GaloisField 3 2) 3 1 (n + 1) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (n + 1)) ∧
      ∀ i : Fin n, (Phan.blockEmb2 (GaloisField 3 2) 3 1 n i).range.map ψ = U i

@[expose] def PhanChain3U {G : Type} [Group G] (K : Subgroup G) (m : ℕ) : Prop :=
  ∃ U : Fin (m + 2) → Subgroup G, (∀ i, U i ∈ conjClass3 K) ∧
    (∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
    (∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
      ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (U i) (U j)) ∧
    ∀ i j k : Fin (m + 2), (j : ℕ) = i + 1 → (k : ℕ) = j + 1 →
      ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G,
        θ.range = (U i ⊔ U j) ⊔ (U j ⊔ U k) ∧
          θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
          (Phan.blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = U i ∧
          (Phan.blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = U j ∧
          (Phan.blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = U k

@[expose] def ChainRow3U (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .PSU (m + 1)) (conjClass3 K) z → PhanChain3U K m

end CFSG.ClassicalInvolution.Q3.Q3W
