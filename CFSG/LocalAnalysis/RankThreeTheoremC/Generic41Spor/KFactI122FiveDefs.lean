module

public import CFSG.Open.Defs
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)

@[expose] def FiveDiagType (K : Type) [Group K] : Prop :=
  (∃ n ℓ f : ℕ, StatedClassicalModel K .PSL n ℓ f ∧ 5 ∣ Nat.gcd n (ℓ ^ f - 1)) ∨
    ∃ n ℓ f : ℕ, StatedClassicalModel K .PSU n ℓ f ∧ 5 ∣ Nat.gcd n (ℓ ^ f + 1)

@[expose] def Sylow5OmegaLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → (∃ (t : StatedLieTag) (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f ∧
      LieModel K t n ℓ f) → ∀ S : Sylow 5 K, Nat.card S = 5 ^ 5 →
      IsMulCommutative (Subgroup.closure {g : K | g ∈ (S : Subgroup K) ∧ g ^ 5 = 1}) →
        IsMulCommutative (S : Subgroup K)

@[expose] def FiveDiagSylow : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → FiveDiagType K → ∀ S : Sylow 5 K,
      5 ^ 6 ≤ Nat.card S ∨ (5 ^ 4 ≤ Nat.card S ∧ ∀ s ∈ (S : Subgroup K), s ^ 5 = 1)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
