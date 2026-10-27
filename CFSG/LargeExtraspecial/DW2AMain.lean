module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.DWRed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_maximal_singular {W₀ : Submodule (ZMod 2) S.Qt} (hi : IsMbarInvariant S W₀)
    (hs : ∀ v ∈ W₀, S.q v = 0) :
    ∃ W₁ : Submodule (ZMod 2) S.Qt, IsMbarInvariant S W₁ ∧ (∀ v ∈ W₁, S.q v = 0) ∧ W₀ ≤ W₁ ∧
      ∀ U : Submodule (ZMod 2) S.Qt, IsMbarInvariant S U → (∀ v ∈ U, S.q v = 0) → W₁ ≤ U →
        U = W₁ := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨W₁, ⟨h1, h2, h3⟩, hmax⟩ := (wellFounded_gt (α := Submodule (ZMod 2) S.Qt)).has_min
    {U | IsMbarInvariant S U ∧ (∀ v ∈ U, S.q v = 0) ∧ W₀ ≤ U} ⟨W₀, hi, hs, le_rfl⟩
  refine ⟨W₁, h1, h2, h3, fun U hU hUs hle => ?_⟩
  by_contra hne
  exact hmax U ⟨hU, hUs, h3.trans hle⟩ (lt_of_le_of_ne hle (Ne.symm hne))

variable [IsSimpleGroup G]

end CFSG.LargeExtraspecial.DW
