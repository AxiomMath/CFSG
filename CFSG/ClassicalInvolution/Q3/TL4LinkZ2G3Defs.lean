module

public import CFSG.ClassicalInvolution.Uniform.ULieType
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform

section Cit3


@[expose] def OrthThreeCommuting (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∀ R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n 3 1 Nat.prime_three).D,
    ∃ g : Fin 3 → (Generic.modelUniv t n 3 1 Nat.prime_three).K,
      ∀ i j, i ≠ j → ∀ x ∈ conjSub (g i) R, ∀ y ∈ conjSub (g j) R, x * y = y * x

@[expose] def OrthThreeCommutingFacts : Prop :=
  (∀ n, 4 ≤ n → OrthThreeCommuting .POmegaOdd n) ∧
    (∀ n, 4 ≤ n → OrthThreeCommuting .POmegaPlus n) ∧
    (∀ n, 5 ≤ n → OrthThreeCommuting .POmegaMinus n)

@[expose] def OrthFundCover (Y : Type) [Group Y] (K₀ : Subgroup Y) (d : ℕ) (ε : Bool) : Prop :=
  ∃ M₀ : Subgroup Y, K₀ ≤ M₀ ∧ HasOrthTypeU 3 1 (CoreAssembly.conjClass M₀) d ε

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
