module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma517_of (h37 : Asc82Lemma37) (h513 : Asc82Lemma513) (h514 : Asc82Lemma514)
    (h515b : Asc82Lemma515b) (h515c : Asc82Lemma515c) (fuse : Asc82Fact517Fuse)
    (swap : Asc82FactSwap6) : Asc82Lemma517 := by
  intro G _ _ t L S z r B A K₁ K₂ h c
  exact ⟨sec5b517_perm h37 h514 h515b h515c fuse c,
    sec5b517_trans h37 h513 h514 h515b swap c⟩

end CFSG.OddStandard.SmallF3.Omega
