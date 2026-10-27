module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Assembly.LowTwoRank

theorem OddRankLeOne.sqt_bound {S : Type} [Group S] [Finite S] (h : OddRankLeOne S) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2 := by
  intro q hq hq2
  have := h q hq hq2
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at this
  omega

theorem oddRankOneOddClassical : OddRankOneOddClassicalProp := by
  intro S _ _ hS p hp hp2 t n f h
  have hres := CFSG.SectionRank.sqt_odd_classical_restriction hS.sqt_bound hp2 h
  obtain ⟨-, hf, hr⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 := by
    have := hS p hp hp2
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at this
  rcases hres with ⟨rfl, rfl, hf12⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    have hf1 : f = 1 := by
      rcases hr with ⟨-, ⟨-, hfr⟩ | ⟨h3, -⟩ | h4⟩ | ⟨h5, -⟩ | ⟨h5, -⟩ | h4 <;>
        first | omega | (exfalso; simp at h5)
    subst hf1
    have hne : p ≠ 3 := by
      rintro rfl
      exact h.1.2.2.2.2 rfl
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have := hp.two_le
    refine ⟨rfl, rfl, rfl, ?_⟩
    omega
  ·
    exfalso
    rcases hr with ⟨-, ⟨h3, -⟩ | ⟨-, hfr⟩ | h4⟩ | ⟨h5, -⟩ | ⟨h5, -⟩ | h4 <;>
      first | omega | (simp at h3) | (simp at h5)
  ·
    exfalso
    rcases hr with ⟨h5, -⟩ | ⟨-, ⟨-, hfr⟩ | h4⟩ | ⟨h5, -⟩ | h4 <;>
      first | omega | (simp at h5)

end CFSG.QuasithinUnique.Setup.Family
