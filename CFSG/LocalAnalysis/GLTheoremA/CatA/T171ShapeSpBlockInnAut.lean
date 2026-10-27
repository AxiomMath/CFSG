module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedRecipe
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockComm
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinTwoFam
public import CFSG.LieType.SeitzGeneration.OuterLinearCat
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInSpTransFactor
public import CFSG.Sporadic.Schreier.Fi22Schreier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr
  inner_le_innAutDerived)

theorem innAutDerived_projConj_statedSL {N : ℕ} {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (B : GL (Fin N) K)
    (hB : B ∈ Subgroup.normalizer (StatedSL N K : Set (GL (Fin N) K)))
    (hBp : B ^ p = 1) :
    TableB.projConj (StatedSL N K) ⟨B, hB⟩ ∈
      innAutDerived (LargeEvenProj (StatedSL N K)) := by
  have hBlin : LinearFlag.conjAut N K B ∈ LinearFlag.linearAutGroup N K :=
    LinearFlag.mem_linearAutGroup_iff.mpr ⟨B, rfl⟩
  have hBpow : LinearFlag.conjAut N K B ^ p = 1 := by
    rw [← map_pow, hBp, map_one]
  have hmem : LinearFlag.conjAut N K B ∈ innAutDerived (LinearFlag.projectiveSL N K) :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.mem_innAutDerived_of_mem_linearAutGroup hp hp2
      hBpow hBlin
  have h := statedProjConj_recipe (N := N) (K := K) B hB
  exact (mem_innAutDerived_congr (statedRecipeEquiv N K).symm).mp (h ▸ hmem)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
