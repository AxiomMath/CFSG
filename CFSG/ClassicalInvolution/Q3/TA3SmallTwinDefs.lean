module

public import CFSG.ClassicalInvolution.Q3.TA3SmallDefs
public import CFSG.GH74.E2.Shapes
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinFrame
public import CFSG.GH74.L5U5.ModelsInvolution

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5

@[expose] def SL4FrameOuterQ8Free : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F % 4 = 3 →
    FrameOuterQ8Free ↥(ModelData.lin F).K4 (ModelData.lin F).J2 (ModelData.lin F).J4

@[expose] def SU4FrameOuterQ8Free : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2), p ^ f % 4 = 1 →
    FrameOuterQ8Free ↥(ModelData.uni hF).K4 (ModelData.uni hF).J2 (ModelData.uni hF).J4

section Leaves


@[expose] def TwinLeafAt (P : ∀ (K : Type) [Group K], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → TightFStarQuasisimple Y →
    TwoSubgroupsFourGenerated (genFittingFStar Y) → P ↥(genFittingFStar Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → ∀ c ∈ fstarCenter Y, c ≠ 1 → (∃ y : Y, y * t * y⁻¹ = t * c) →
        GoodThreeElement R t

@[expose] def Twin2M12Leaf : Prop := TwinLeafAt fun K _ => GH74.E2.Shape2M12 K

@[expose] def Twin2Sz8Leaf : Prop := TwinLeafAt fun K _ => GH74.E2.Shape2Sz8 K

@[expose] def Twin2AnLeaf : Prop :=
  TwinLeafAt fun K _ => ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ GH74.GLS.IsDoubleCoverOfAlt K n

end Leaves

end CFSG.ClassicalInvolution.Q3.TA3
