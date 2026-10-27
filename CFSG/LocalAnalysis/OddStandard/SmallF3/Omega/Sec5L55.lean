module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L55a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L55b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma55_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (h54 : Asc82Lemma54) (hO : Asc82Outside)
    (tab : Asc82Tab5) : Asc82Lemma55 := by
  intro G _ _ t L S z h
  by_cases hconj : ∃ h' : G, h'⁻¹ * t * h' = t * z
  · exact Or.inl hconj
  · refine Or.inr fun g hsC hne => ?_
    have hs2 : orderOf (g⁻¹ * t * g) = 2 := by rw [orderOf_conjugate_eq]; exact h.involution
    have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
      sec4_mem_normalizer h36 h.toSec3SettingLB _ hsC
    rcases tab.classify G L h.toSec5Setting.isOm6Z2 _ hs2 hsN with
      hc | h0 | h1 | h2 | h3 | h4 | h5
    · exact (sec5_case_central h52a h.toSec5Setting hsC hne hc).elim
    · exact (hconj (sec5_case_inner h37 h52a h52b tab h hsC hne h0)).elim
    · exact (sec5_case_i4m h36 h37 h52a h52b h53 h54 hO tab h hsC hne h1).elim
    · exact h2
    · exact (hconj (sec5_case_cover h36 h52a h52b h54 hO tab h hsC hne (Or.inl h3))).elim
    · exact (hconj (sec5_case_cover h36 h52a h52b h54 hO tab h hsC hne (Or.inr (Or.inl h4)))).elim
    · exact (hconj (sec5_case_cover h36 h52a h52b h54 hO tab h hsC hne (Or.inr (Or.inr h5)))).elim

end CFSG.OddStandard.SmallF3.Omega
