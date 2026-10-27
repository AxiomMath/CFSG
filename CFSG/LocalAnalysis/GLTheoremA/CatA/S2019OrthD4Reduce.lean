module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalPartsSO
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4Field
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

@[expose] def S2019OrthD4Graph : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q f : ℕ), q.Prime → q ≠ 2 → q ≠ 3 → Nat.card K = q ^ f →
    ∀ t : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)), t ^ 3 = 1 →
      t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K) → S2019FixCentralizes 3 t

theorem s2019OrthD4Outer_of_graph (h : S2019OrthD4Graph) : S2019OrthD4Outer := by
  intro q hq hq2 hq3 G _ f hG β hβ hnot
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  by_cases hE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus 4 K)
  · exact s2019FixCentralizes_omega_plus_of_mem_E hG hq2 Nat.prime_three (by norm_num) hK e β hβ
      hnot hE
  · haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
    exact s2019FixCentralizes_of_congr Nat.prime_three (coordinatePlusWitnessEquiv K e) β
      (h K q f hq hq2 hq3 hK _ (by rw [← map_pow, hβ, map_one]) hE)

end CFSG.LocalAnalysis.GLTheoremA.S2019
