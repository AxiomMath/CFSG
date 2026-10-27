module

public import CFSG.Milestones.FAM_classical_model_membership
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
import CFSG.HardMathSupport.Foote.Proving.ModelFinite
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.LieType.Simplicity

open Matrix CFSG.Assembly.LowTwoRank

theorem fam_PSL_simplicity (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .PSL n p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨⟨hp, hf, hn, h22, h23⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hs : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin n) K) := by
    refine CFSG.BenderSuzuki.External.huppert_II_6_13 n hn ?_ ?_
    · by_cases hn2 : n = 2
      · exact .inr fun h2 => h22 (by rw [hn2, ← hK, h2])
      · exact .inl hn2
    · by_cases hn2 : n = 2
      · exact .inr fun h3 => h23 (by rw [hn2, ← hK, h3])
      · exact .inl hn2
  have hG : IsSimpleGroup G :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).isSimpleGroup
  exact ⟨hG.toNontrivial, hG⟩

theorem finite_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (H : Subgroup (GL ι K)) : Finite (StatedProj H) :=
  inferInstance

theorem finite_of_statedClassicalModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) : Finite G :=
  CFSG.HardMathSupport.Foote.Proving.finite_of_statedClassicalModel _ _ _ _ _ h

theorem fam_classical_finiteness (G : Type) [Group G] (h : Milestones.ClassicalRep G) :
    Finite G := by
  obtain ⟨t, n, p, f, h⟩ := h
  exact finite_of_statedClassicalModel h

theorem fam_classical_converse (G : Type) [Group G] (h : Milestones.ClassicalRep G) :
    Finite G ∧ Nontrivial G ∧ IsSimpleGroup G := by
  refine ⟨fam_classical_finiteness G h, ?_⟩
  obtain ⟨t, n, p, f, h⟩ := h
  cases t with
  | PSL => exact fam_PSL_simplicity G n p f h
  | PSU => exact CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity G n p f h
  | PSp =>
    have hG := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp G n p f h
    exact ⟨hG.toNontrivial, hG⟩
  | POmegaOdd =>
    exact CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaOdd G n p f h
  | POmegaPlus =>
    exact CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus G n p f h
  | POmegaMinus =>
    exact CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus G n p f
      h
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact h.2.elim

end CFSG.LieType.Simplicity
