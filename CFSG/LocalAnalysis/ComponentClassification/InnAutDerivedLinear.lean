module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagPSL2
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagPSLn
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearTwo

public section

namespace CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.GorensteinWalter

theorem innAutDerived_projectiveSL_two_le_linearAutGroup {K : Type} [Field K] [Finite K] :
    innAutDerived (projectiveSL 2 K) ≤ linearAutGroup 2 K := by
  intro α hα
  rw [mem_linearAutGroup_iff]
  have hα' : MulAut.congr (psl2Equiv K).symm α ∈ innAutDerived (PSL2 K) :=
    (mem_innAutDerived_congr (psl2Equiv K).symm).2 hα
  have hmem : MulAut.congr (psl2Equiv K).symm α ∈ (pglAction K).range :=
    innAutDerived_le_stdPinnedPSL2_inndiag K hα'
  obtain ⟨g, hg⟩ := hmem
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [← hA] at hg
  refine ⟨A, ?_⟩
  calc conjAut 2 K A
      = MulAut.congr (psl2Equiv K) (pglAction K (Matrix.ProjGenLinGroup.mk A)) :=
        (congr_pglAction_mk (K := K) A).symm
    _ = MulAut.congr (psl2Equiv K) (MulAut.congr (psl2Equiv K).symm α) := by rw [hg]
    _ = α := by
        ext x
        simp [MulAut.congr_apply]

theorem innAutDerived_projectiveSL_le_linearAutGroup {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K]
    [Finite K] : innAutDerived (projectiveSL m K) ≤ linearAutGroup m K := by
  rcases Nat.lt_or_ge m 3 with h | h
  · have hm2 : m = 2 := by omega
    subst hm2
    exact innAutDerived_projectiveSL_two_le_linearAutGroup
  · exact CFSG.HardMathSupport.Solomon.Coordinator.innAutDerived_le_linearAutGroup h

end CFSG.ComponentClassification.OuterAutomorphisms

end
