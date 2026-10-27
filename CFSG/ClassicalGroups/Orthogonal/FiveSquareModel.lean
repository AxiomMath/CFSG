module

public import CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.FiveSquareModel

open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration

public theorem lieModel_derived :
    CFSG.Blueprint.LieModel
      ↥CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.derived .PSp 2 5 1 := by
  have hodd : Odd (Nat.card F) := by
    rw [Nat.card_zmod]
    norm_num
  have hdim : Module.finrank F (Fin 5 → F) = 5 := by
    simpa using Module.finrank_fin_fun (R := F) (n := 5)
  letI : AddCommGroup (Fin 5 → F) :=
    { Pi.addCommGroup with toAddCommMonoid := Pi.addCommMonoid }
  letI : Module F (Fin 5 → F) := Pi.Function.module (Fin 5) F F
  haveI : FiniteDimensional F (Fin 5 → F) := inferInstance
  obtain ⟨_, _, eO, _, _, _⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalFive.finite_odd_five_selfAdjoint_form_similarity
      (K := F) (Q := Q) hodd (Generic.polar_nondegenerate F) hdim
  let eComm : ↥(commutator O) ≃*
      ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointForm F))) :=
    MulEquiv.commutatorCongr eO
  let eP := CFSG.ClassicalGroups.Symplectic.pspFourEquivDerivedOrthogonal (K := F) hodd
  let eD : ↥derived ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F) :=
    CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups.eD0.symm.trans
      (eComm.trans eP.symm)
  refine Or.inl ⟨by decide, ?_⟩
  unfold CFSG.Open.StatedClassicalModel
  dsimp only
  refine ⟨?_, F, inferInstance, inferInstance, ?_, ⟨eD⟩⟩
  · exact ⟨Nat.prime_five, le_rfl, le_rfl, by norm_num⟩
  · rw [Nat.card_zmod]
    norm_num

public theorem exists_noncommuting_derived :
    ∃ a b : ↥CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.derived,
      a * b ≠ b * a := by
  have hne : zCentralizer ≠ ⊤ := ne_of_lt zCentralizer_lt_top
  have hex : ∃ g : ↥derived, g ∉ zCentralizer := by
    by_contra h
    apply hne
    rw [eq_top_iff]
    intro g _
    by_contra hg
    exact h ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hex
  exact ⟨g, zD, fun hcomm => hg (mem_zCentralizer_iff.mpr hcomm)⟩

end CFSG.ClassicalGroups.Orthogonal.FiveSquareModel
