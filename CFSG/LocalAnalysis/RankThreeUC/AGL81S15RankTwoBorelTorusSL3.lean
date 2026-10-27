module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBorelTorus
import CFSG.ClassicalGroups.SpecialLinear.DiagTorusNormalizesUnitriangular
import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRankTwo
import CFSG.Quasithin.SteinbergBIEvenLinearThreeThreeSylowAction
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.SpecialLinear

theorem hasBorelTorus_specialLinear_three {F : Type} [Field F] [Finite F] [CharP F 2] {q : ℕ}
    (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1)
    {U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    HasBorelTorus (Matrix.SpecialLinearGroup (Fin 3) F) q U := by
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf (LinearFlag.unitriangular 3 F) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hP]
      exact P.isPGroup'
    · rw [CFSG.QuasithinUnique.index_subgroupOf_top, ← hP]
      exact P.not_dvd_index
  obtain ⟨E, hE_diag, hE_elem, hE_card⟩ :=
    exists_elemAbelian_sq (Y := Matrix.SpecialLinearGroup (Fin 3) F) hq
      (two_le_pRank_diagTorus hq hdvd)
  refine HasBorelTorus.of_isSylowTwoOf hU₀ hU ⟨E, ?_⟩
  refine ⟨?_, hE_elem, hE_card, ?_⟩
  · exact hE_diag.trans CFSG.diagTorus_le_normalizer_unitriangular
  · intro a ha e he
    have haU : a ∈ LinearFlag.upperTriangular 3 F := by
      rw [← LinearFlag.normalizer_unitriangular]
      exact ha
    have heU : e ∈ LinearFlag.upperTriangular 3 F :=
      CFSG.diagTorus_le_upperTriangular (hE_diag he)
    exact CFSG.Quasithin.SteinbergBI.commutator_mem_unitriangular haU heU

end CFSG.LocalAnalysis.RankThreeUC.S15

end
