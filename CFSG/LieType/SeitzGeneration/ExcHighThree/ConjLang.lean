module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLang

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section LangGamma


theorem lang_graphFixed_E6 (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k]
    [CharP k p] (e : ℕ) (he : 1 ≤ e) (ε : ℕ) :
    ∀ c ∈ graphCentralizer TwistTag.E6.tag k (diagramMap TwistTag.E6 k),
      ∃ z ∈ graphCentralizer TwistTag.E6.tag k (diagramMap TwistTag.E6 k),
        z⁻¹ * (diagramMap TwistTag.E6 k ^ ε *
          Units.map (entrywiseHom (iterateFrobenius k p e)) z *
            (diagramMap TwistTag.E6 k ^ ε)⁻¹) = c := by
  have hA : diagramMap TwistTag.E6 k =
      rootDiagUnit TwistTag.E6.tag (1 : Fin TwistTag.E6.tag.rank → kˣ) *
        diagramMap TwistTag.E6 k := by
    rw [rootDiagUnit_one, one_mul]
  obtain ⟨hZ, -, -, -⟩ := graphCentralizer_realization _
    (isPointIrreducible_e6DiagramCentralizer (k := k))
  obtain ⟨σ, -, -, hlang⟩ := exists_frobTwist_restriction p hZ he (diagramMap TwistTag.E6 k ^ ε)
    fun g hg => by
      have h := frobTwistGL_diagramMap_pow_mem p (c := 1) (fun _ => Or.inl rfl) rfl e ε
        (g := g) (by rwa [← hA])
      rwa [← hA] at h
  exact hlang

end LangGamma

end CFSG.LieType.SeitzGeneration.ExcHighThree
