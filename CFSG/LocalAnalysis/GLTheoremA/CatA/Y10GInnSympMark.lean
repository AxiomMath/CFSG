module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympMark

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem innDiagKind_symp_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamSymp labK) (hin : InnDiagKind S labK α) :
    (canonLabel labK).n = 1 ∨
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ), 2 ≤ m ∧
        Nat.card K = 2 ^ (canonLabel labK).n ∧
        ∃ (e : S ≃* StatedProj (StatedSp m K)) (A : gsp m K),
          ∀ l : S, e (α l) = conjAut m K A (e l) := by
  unfold InnDiagKind CFSG.Assembly.LargeEvenMarking at hin
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ht | ht
  pick_goal 3
  ·
    left
    simp [canonLabel, ht]
  all_goals
    right
    have hm : 2 ≤ labK.rank := by
      have h := hlam
      simp only [LargeEvenInLambda2, ht] at h
      exact h.2.1
    unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeSymplectic at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, hA⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hu
    let e : S ≃* StatedProj (StatedSp labK.rank K) :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans
        QuotientGroup.quotientBot).symm.trans θ
    have hαu : ∀ l : S, e (α l) = conjAut labK.rank K A (e l) := by
      intro l
      rw [hA]
      exact (hind l (α l) rfl).symm
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, ht]
    exact ⟨K, hK, hKf, labK.rank, hm, by rw [hc]; exact hcard, e, A, hαu⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympMark

end
