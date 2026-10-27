module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerOrthDim2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerOrthHigh
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerOrthSplit

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal

theorem oddPCoreInClosure_orthogonalGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (QuadraticMap.polarBilin R).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    OddPCoreInClosure p ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  classical
  by_cases hd2 : finrank K W ≤ 2
  · exact oddPCoreInClosure_orthogonalGroup_of_finrank_le_two R hR hd2 hp hp2
  by_cases hT : ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, R u = 0
  · exact oddPCoreInClosure_orthogonalGroup_of_threeSingular R hR hT hp hp2
  obtain ⟨⟨n, hn⟩, -, hforms, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms R hR
  by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, R u = 0
  ·
    obtain ⟨U, hUn, hUQ⟩ := hS
    have hn2 : n = 2 := by
      by_contra hne
      exact hT (exists_threeSingular_of_le R hUQ (by omega))
    subst hn2
    exact oddPCoreInClosure_orthogonalGroup_splitFour R hR (by omega) ⟨U, hUn, hUQ⟩ hp hp2
  · have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, R u ≠ 0 := by
      intro U hU
      by_contra hcon
      push Not at hcon
      exact hS ⟨U, hU, hcon⟩
    rcases hforms n (by omega) hn with ⟨b, hb⟩ | ⟨β, γ, -, -, b, hb⟩
    · exfalso
      refine hS ⟨Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)), ?_, ?_⟩
      · exact (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans
          (by simp)
      · intro u hu
        obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
        simpa using hb x 0
    ·
      have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)),
          R u = 0 := by
        intro u hu
        obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
        simpa using hb x 0 0 0
      have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) =>
          b (Sum.inl i))) = n - 1 :=
        (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
      have hn23 : n = 2 ∨ n = 3 := by
        by_contra hne
        exact hT (exists_threeSingular_of_le R hU (by omega))
      exact oddPCoreInClosure_orthogonalGroup_nonsplit R hR (by omega)
        (fun U hU' => hts U (by omega)) hp hp2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
