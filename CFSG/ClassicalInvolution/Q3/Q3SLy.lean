module

public import CFSG.ClassicalInvolution.Q3.Q3SCriteria
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Th CFSG.Perm CFSG.Sporadic.Ly
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.LyProof

theorem noWeakClassical3_J : NoWeakClassical3 J := by
  obtain ⟨hCK, hq, hcen, hcard⟩ := K_facts
  obtain ⟨hSp, hidx⟩ := S_sylow
  obtain ⟨-, hcover⟩ := S_facts
  have htop : NoWeakClassical3 (⊤ : Subgroup J) := by
    refine noWeakClassical3_of_single_class_quasisimple (⊤ : Subgroup J) SJ KJ hSp hidx
      (Subgroup.mem_top zJ) ?_ ?_ hq hcen (by rw [hcard]; norm_num)
    · intro s hs hord
      have hss : s * s = 1 := by
        have := pow_orderOf_eq_one s
        rwa [hord, pow_two] at this
      have hs1 : s ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hord
        exact absurd hord (by norm_num)
      obtain ⟨C, hC⟩ := hcover s hs hss hs1
      exact ⟨C, Subgroup.mem_top C, hC⟩
    · rw [CFSG.Sporadic.Schreier.centralizerIn, top_inf_eq]
      exact hCK
  have e : GrpEquiv J (⊤ : Subgroup J) := (Subgroup.topEquiv (G := J)).symm
  exact NoWeakClassical3.of_mulEquiv e htop

theorem noWeakClassical3_Ly : NoWeakClassical3 (Carrier .Ly) := by
  have e : GrpEquiv (Carrier .Ly) J := lyEquivJ
  exact NoWeakClassical3.of_mulEquiv e noWeakClassical3_J

end CFSG.ClassicalInvolution.Q3
