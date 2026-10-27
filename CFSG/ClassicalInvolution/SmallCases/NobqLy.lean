module

public import CFSG.ClassicalInvolution.SmallCases.NobqQuasi
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.SmallCases.NobqLists
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Sporadic.Th CFSG.Perm CFSG.Sporadic.Ly CFSG.ClassicalInvolution.LyProof

theorem noUniqueInvNormal_J : NoUniqueInvNormal J := by
  obtain ⟨hCK, hq, hcen, -⟩ := K_facts
  obtain ⟨hSp, hidx⟩ := S_sylow
  obtain ⟨-, hcover⟩ := S_facts
  have hSr : ∀ s ∈ SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup J), s = c * zJ * c⁻¹ := by
    intro s hs ho
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [ho, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at ho
      exact absurd ho (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩
  have htop : NoUniqueInvNormal (⊤ : Subgroup J) := by
    refine noUniqueInvNormal_of_reps (⊤ : Subgroup J) [zJ] (fun r hr => ?_) (fun u hu ho => ?_)
      (fun r hr hrH N => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact Subgroup.mem_top _
    · obtain ⟨c, hc, hcu⟩ := cover_of_sylow ⊤ SJ hSp hidx zJ hSr u hu ho
      exact ⟨zJ, by simp, c, hc, hcu⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      obtain ⟨u, huK, hu2, hu1, hur⟩ := exists_noncentral_involution
      exact not_uniqueInvNormal_of_ambient_quasisimple ⊤ _ hrH KJ
        (by rw [CFSG.Sporadic.Schreier.centralizerIn, top_inf_eq]; exact hCK) hq hcen u huK hu2 hu1
        hur N
  have e : GrpEquiv J (⊤ : Subgroup J) := (Subgroup.topEquiv (G := J)).symm
  exact NoUniqueInvNormal.of_mulEquiv e htop

theorem noUniqueInvNormal_Ly : NoUniqueInvNormal CFSG.Blueprint.NativeSporadic.Ly := by
  have e : GrpEquiv CFSG.Blueprint.NativeSporadic.Ly J := lyEquivJ
  exact NoUniqueInvNormal.of_mulEquiv e noUniqueInvNormal_J

end CFSG.ClassicalInvolution.Nobq
