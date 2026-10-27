module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticGeometry

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddQuadratic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] [Finite K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_original_hyperbolic_decomposition (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) :
    ∃ (m : ℕ) (P : Fin m → HypPair Q) (A : Submodule K V),
      Module.finrank K A ≤ 2 ∧ (Q.restrict A).Anisotropic ∧
      Module.finrank K V = 2 * m + Module.finrank K A ∧
      (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
      (∀ i, Module.finrank K (Submodule.span K {(P i).e, (P i).f}) = 2 ∧
        Nonempty ((hyperbolicPairForm K).IsometryEquiv
          (Q.restrict (Submodule.span K {(P i).e, (P i).f})))) ∧
      A = ⨅ i, (P i).perp ∧
      A = LinearMap.BilinForm.orthogonal Q.polarBilin
        (⨆ i, Submodule.span K {(P i).e, (P i).f}) ∧
      IsCompl (⨆ i, Submodule.span K {(P i).e, (P i).f}) A ∧
      Nonempty (Q.IsometryEquiv ((hyperbolicSumForm K m).prod (Q.restrict A))) := by
  obtain ⟨m, k, w, hk, hani, hrank, ⟨e⟩⟩ := exists_hyperbolic_decomposition hodd Q hQ
  have hA : Module.finrank K (residualSubspace e) = k := by
    rw [residualSubspace_finrank, Module.finrank_pi, Fintype.card_fin]
  have hplanes : (⨆ i, Submodule.span K {(originalHypPair e i).e,
      (originalHypPair e i).f}) = hyperbolicSubspace e := by
    simp_rw [← planeSubspace_eq_span]
    exact (hyperbolicSubspace_eq_iSup_planes e).symm
  refine ⟨m, originalHypPair e, residualSubspace e, ?_,
    residualSubspace_anisotropic e hani, ?_, ?_, ?_,
    residualSubspace_eq_iInf_perp e, ?_, ?_, ?_⟩
  · rwa [hA]
  · rwa [hA]
  · intro i j hij
    exact originalHypPair_orth e hij
  · intro i
    rw [← planeSubspace_eq_span]
    exact ⟨planeSubspace_finrank e i, ⟨planeSubspaceEquiv e i⟩⟩
  · rw [hplanes]
    exact residualSubspace_eq_orthogonal e
  · rw [hplanes]
    exact hyperbolic_residual_isCompl e
  · exact ⟨e.trans ((IsometryEquiv.refl _).prod (residualSubspaceEquiv e))⟩

theorem exists_three_original_hypPairs_of_seven_le (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 7 ≤ Module.finrank K V) :
    ∃ P₁ P₂ P₃ : HypPair Q, P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃ := by
  obtain ⟨m, k, w, hk, _, hrank, ⟨e⟩⟩ := exists_hyperbolic_decomposition hodd Q hQ
  have hm : 3 ≤ m := by omega
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  let i₂ : Fin m := ⟨2, by omega⟩
  refine ⟨originalHypPair e i₀, originalHypPair e i₁, originalHypPair e i₂,
    originalHypPair_orth e ?_, originalHypPair_orth e ?_, originalHypPair_orth e ?_⟩
  all_goals
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁, i₂] at this

theorem exists_totallySingular_of_seven_le (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 7 ≤ Module.finrank K V) :
    ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ :=
    exists_three_original_hypPairs_of_seven_le hodd Q hQ hdim
  exact exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃

theorem finrank_le_six_of_no_totallySingular_three (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hno : ¬ ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Module.finrank K V ≤ 6 := by
  by_contra hdim
  exact hno (exists_totallySingular_of_seven_le hodd Q hQ (by omega))

end CFSG.ComponentClassification.CatalogueBOddQuadratic
