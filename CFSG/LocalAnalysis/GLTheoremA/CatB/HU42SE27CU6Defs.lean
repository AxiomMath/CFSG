module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

abbrev Z6 : Subgroup M6 := (StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4)

@[expose] def U6NineFact : Prop :=
  ∀ (B : primeFormUnitary hF4 (idGram F4 6)) (c : F4ˣ), c ≠ 1 →
    (B : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c →
    ∀ J : Subgroup M6, J ≤ CenD (B : GL (Fin 6) F4) → ⁅J, J⁆ = J → Nat.card ↥J ∣ 504

@[expose] def U6CubeFact : Prop :=
  ∀ s : M6, s ^ 3 = 1 → s ∉ Z6 →
    (∀ J : Subgroup M6, J ≤ CenD (s : GL (Fin 6) F4) → ⁅J, J⁆ = J → J = ⊥) ∨
    ∃ R : Subgroup M6, R ≤ CenD (s : GL (Fin 6) F4) ∧ IsSimpleGroup ↥R ∧
      ¬ IsMulCommutative ↥R ∧ Nat.card ↥R = 25920 ∧ R ⊓ Z6 = ⊥ ∧
      (∀ g : M6, ∀ z ∈ Z6, g * s * g⁻¹ = s * z → g ∈ CenD (s : GL (Fin 6) F4)) ∧
      (∀ g ∈ CenD (s : GL (Fin 6) F4), ∃ n : ℕ, ∃ z ∈ Z6, ∃ r ∈ R, g = s ^ n * z * r) ∧
      (∀ z ∈ Z6, ∀ r ∈ R, s ≠ z * r)

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
