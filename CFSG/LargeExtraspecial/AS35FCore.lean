module

public import CFSG.LargeExtraspecial.AS35DStmt
public import CFSG.LargeExtraspecial.FS77Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S14

theorem aschbacherSmith35Core_of_main (h : AschbacherMainStmt) (h65 : SmithSixFiveStmt) :
    AschbacherSmith35Core := by
  intro G _ _ _ S hn hW
  have hA : S.AschbacherHyp := h65 G S hn hW
  have htop : S.zGen = ⊤ := S.closure_conj_eq_top
  rcases h G S (by omega) with h1 | ⟨-, -, h3 | ⟨hw, ⟨e⟩⟩⟩ | ⟨t, htQ, ht2, ht⟩ | ⟨g, hgQ, hgne⟩
  · rw [S.center_eq_bot, mem_bot] at h1
    exact (S.z_ne_one h1).elim
  · exact Or.inl fun g₁ g₂ => h3 g₁ (htop ▸ mem_top _) g₂ (htop ▸ mem_top _)
  · exact Or.inr ⟨hw,
      ⟨((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩⟩
  · refine (ht (hA t htQ ?_)).elim
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  · exact (hgne (hW g hgQ)).elim

end S14

namespace FS77

theorem fSmith1977cW4WeakInput_of_main (h : S14.AschbacherMainStmt)
    (h65 : S14.SmithSixFiveStmt) : FSmith1977cW4WeakInput :=
  fSmith1977cW4WeakInput_of_core35 (S14.aschbacherSmith35Core_of_main h h65)

end FS77

end CFSG.LargeExtraspecial
