module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelDefs
public import CFSG.Open.StatedZModTwo
public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockAnalysis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockProofFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonalLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.StandardType CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem projConj_mem_inner_of_scalar_mul {a : ℕ} {E : Type} [Field E] (B : GL (Fin a) E)
    {μ : Eˣ} {s : GL (Fin a) E} (hs : s ∈ StatedSL a E)
    (hB : B = Matrix.GeneralLinearGroup.scalar (Fin a) μ * s) :
    TableB.projConj (StatedSL a E)
        ⟨B, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top B⟩ ∈
      inner (LargeEvenProj (StatedSL a E)) := by
  have hscalarN : Matrix.GeneralLinearGroup.scalar (Fin a) μ ∈
      Subgroup.normalizer (StatedSL a E : Set (GL (Fin a) E)) :=
    TableB.scalar_mem_normalizer (StatedSL a E) ⟨μ, rfl⟩
  have hsN : s ∈ Subgroup.normalizer (StatedSL a E : Set (GL (Fin a) E)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top s
  have hBN : B ∈ Subgroup.normalizer (StatedSL a E : Set (GL (Fin a) E)) := by
    rw [hB]
    exact Subgroup.mul_mem _ hscalarN hsN
  have hEq : TableB.projConj (StatedSL a E)
      ⟨B, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top B⟩ =
      TableB.projConj (StatedSL a E) ⟨s, hsN⟩ := by
    rw [hB]
    exact projConj_scalar_mul (StatedSL a E) μ s hsN (hB ▸ hBN)
  rw [hEq]
  exact ⟨((⟨s, hs⟩ : StatedSL a E) : LargeEvenProj (StatedSL a E)),
    (TableB.projConj_of_mem (StatedSL a E) s hs).symm⟩

theorem projConj_mem_inner_of_card_two {a : ℕ} {E : Type} [Field E] (hE : Nat.card E = 2)
    (B : GL (Fin a) E) :
    TableB.projConj (StatedSL a E)
        ⟨B, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top B⟩ ∈
      inner (LargeEvenProj (StatedSL a E)) := by
  have htop : StatedSL a E = ⊤ := statedSL_eq_top_of_card_two hE a
  have hB : B ∈ StatedSL a E := by rw [htop]; exact Subgroup.mem_top B
  exact ⟨((⟨B, hB⟩ : StatedSL a E) : LargeEvenProj (StatedSL a E)),
    (TableB.projConj_of_mem (StatedSL a E) B hB).symm⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

@[expose] def OrthPairedBlockModelResidual : Prop :=
  ∀ {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V), OrthPairedBlockModel Q

theorem orthPairedBlock_holds_of_model_residual (h : OrthPairedBlockModelResidual) :
    ∀ {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (Q : QuadraticForm K V), OrthPairedBlock Q :=
  fun Q => orthPairedBlock_of_model (h Q)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
