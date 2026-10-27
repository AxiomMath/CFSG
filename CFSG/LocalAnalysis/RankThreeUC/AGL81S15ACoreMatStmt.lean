module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open

@[expose] def LinCoreMatrix : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (m r : ℕ), r.Prime → r ≠ 2 → r ∣ Fintype.card F - 1 →
    r ∣ m → 3 ≤ m → ∀ (Z₀ : Subgroup ↥(StatedSL m F)) [Z₀.Normal],
      Z₀ ≤ (StatedScalars (Fin m) F).subgroupOf (StatedSL m F) →
      CFSG.Open.pRank r (⊤ : Subgroup (↥(StatedSL m F) ⧸ Z₀)) =
        m - 1 - (if padicValNat r (Nat.card Z₀) =
            padicValNat r (Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F))) ∧
            4 ≤ m ∧ padicValNat r (Fintype.card F - 1) ≤ padicValNat r m then 1 else 0)

@[expose] def UniCoreMatrix : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (q m r : ℕ), r.Prime → r ≠ 2 → Fintype.card F = q ^ 2 →
    r ∣ q + 1 → r ∣ m → 3 ≤ m → (m = 3 → 3 ≤ q) →
    ∀ (Z₀ : Subgroup ↥(StatedSU m q F)) [Z₀.Normal],
      Z₀ ≤ (StatedScalars (Fin m) F).subgroupOf (StatedSU m q F) →
      CFSG.Open.pRank r (⊤ : Subgroup (↥(StatedSU m q F) ⧸ Z₀)) =
        m - 1 - (if padicValNat r (Nat.card Z₀) =
            padicValNat r (Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F))) ∧
            4 ≤ m ∧ padicValNat r (q + 1) ≤ padicValNat r m then 1 else 0)

end CFSG.LocalAnalysis.RankThreeUC.S15
