module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.PerfectCommutator
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderMax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
open CFSG.HardMathSupport.Cooperstein
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_of_le_normalizer' {V L : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) : ⁅V, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h := (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
  have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact V.mul_mem hv h

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

end
