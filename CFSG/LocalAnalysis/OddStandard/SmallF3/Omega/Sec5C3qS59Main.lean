module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3q510
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qS59Ctx2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qS59Orb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Sym59_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (h54 : Asc82Lemma54) (hZ : Asc82ZExists)
    (tab : Asc82Tab5) (tab56 : Asc82Tab56) (h58b : Asc82Lemma58b) (h58d : Asc82Lemma58d)
    (n1 : Asc82E64Kind3) (n2 : Asc82Kind2Split) : Asc82Sym59 := by
  intro G _ _ t L S z r B A hR h7 hex
  obtain ⟨g₀, hg₀⟩ := hex
  have hy : Sec5B59Hyp := ⟨h36, h37, h52b, h53, tab, h54, h58b⟩
  obtain ⟨φ, hm⟩ := sec5b_model58_of h58d hR
  obtain ⟨a, hR'⟩ := sec5c3q_s59_ctx2 hy h52a hZ tab56 n1 n2 hR hm hg₀
  obtain ⟨φ', hm'⟩ := sec5b_model58_of h58d hR'
  exact sec5c3q_s59_orbit_contra hy hR hm h7 hg₀ hR' hm'

end CFSG.OddStandard.SmallF3.Omega
