module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddOpen

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.Fischer CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartTwo.Sec11
  CFSG.RankThree.PartTwo.Sec19

section Statements

@[expose] def TriOddClosingXAt (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → (ℓ ^ f) % 3 = r → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ z : C0 σ, z ^ 3 = 1 → z ≠ 1 → TriOddIsClassX σ z →
    ∀ H : Subgroup (C0 σ), Subgroup.centralizer ({z} : Set (C0 σ)) ≤ H →
      (∃ y ∈ H, y * z * y⁻¹ ∉ Subgroup.zpowers z) → H = ⊤

@[expose] def TriOddClosingXPlus : Prop := TriOddClosingXAt 1

end Statements

end CFSG.LieType.SeitzGeneration.ExcWideThree
