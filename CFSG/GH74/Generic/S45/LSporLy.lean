module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.S45.LOrd
public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_map_congr)
open CFSG.ComponentClassification.RestrictedStd.Spor (LyOuterTrivialInput)
open scoped commutatorElement

theorem mem_inner_of_inner_top {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : inner T = ⊤) (α : MulAut S) : α ∈ inner S := by
  have hmem : MulAut.congr e α ∈ (inner S).map (MulAut.congr e).toMonoidHom := by
    rw [inner_map_congr e, h]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxy⟩ := hmem
  have hxa : x = α := (MulAut.congr e).injective hxy
  exact hxa ▸ hx

end CFSG.GH74.Generic.S45
