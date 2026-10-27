module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovAlt
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL34
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovSuz
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL4U4
public import CFSG.GH74.Generic.GKFFinal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL2Sp

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup

theorem fus23Concl_of_cover
    (hI : CF23InnerFusion) (hGA : TBLit.GriessMultipliersAllModels)
    (hSM : SporadicMultTwoPartInput) (hSO : SolMax.SuzOuterComponentsInput)
    (hL4 : CF23L4U4O8Comp) (H : Type) [Group H] [Finite H] (h : Hyp52 H) (hT : ¬ h.Table54)
    (hZK : center (OddBar h.K) ≠ ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f) : h.Fus23Concl := by
  by_cases hKa : conjugate h.K h.a = h.K
  swap
  · exact absurd (table54_of_ne_cover h hKa hZK hJ) hT
  have hGKF := GH74.Generic.genericKnownFacts_of_griess hGA
  have hZJ := center_eq_bot_of_small hJ
  have hres : GSRestricted (ZStarBar h.K) := by
    rcases h.type_K with hr | ⟨hne, -⟩
    · exact hr
    · exact absurd hKa hne
  rcases hres with ⟨p, f, hp, hp2, hf, -, hm⟩ | ⟨p, f, hp, hp2, hf, hm⟩ | ⟨m, -, hm⟩ | hm | hm |
      hm | hm | hm | hm | hm | ⟨n, hn, ⟨e⟩⟩ | hS | hS | hS | hS | hS | hS | hS | hS
  · exact (false_of_psl_two hKa hZK hZJ hp hp2 hm).elim
  · rcases hm with hm | hm | hm | hm | hm | hm | hm
    · exact (false_of_psl_two hKa hZK hZJ hp hp2 hm).elim
    · exact absurd (center_eq_bot_of_psl_three hGKF h hp hp2 hm) hZK
    · exact absurd (center_eq_bot_of_psu_three hGKF h hp hp2 hm) hZK
    · exact absurd (table54_of_l4u4 hKa hL4 hZJ hJ hp hp2 hf (Or.inl hm)) hT
    · exact absurd (table54_of_l4u4 hKa hL4 hZJ hJ hp hp2 hf (Or.inr (Or.inl hm))) hT
    · exact (false_of_psp_four hKa hGKF hZK hZJ hp hp2 hm).elim
    · exact absurd (table54_of_l4u4 hKa hL4 hZJ hJ hp hp2 (by omega)
        (Or.inr (Or.inr ⟨f, rfl, hm⟩))) hT
  · exact absurd (center_eq_bot_of_ree hGKF h hm) hZK
  · exact absurd (center_eq_bot_of_odd_table hGA h (by norm_num) hm (by decide) (by decide)
      (by decide) (by decide)) hZK
  · exact absurd (Or.inr (Or.inl ⟨psl2_five_or_seven_of_psl34 hKa hZJ hJ hm, hKa, hZK, hm⟩)) hT
  · exact absurd (center_eq_bot_of_odd_table hGA h (by norm_num) hm (by decide) (by decide)
      (by decide) (by decide)) hZK
  · exact absurd (center_eq_bot_of_odd_table hGA h (by norm_num) hm (by decide) (by decide)
      (by decide) (by decide)) hZK
  · exact absurd (center_eq_bot_of_odd_table hGA h (by norm_num) hm (by decide) (by decide)
      (by decide) (by decide)) hZK
  · exact absurd (center_eq_bot_of_odd_table hGA h (by norm_num) hm (by decide) (by decide)
      (by decide) (by decide)) hZK
  · exact absurd (center_eq_bot_of_odd_table hGA h (by norm_num) hm (by decide) (by decide)
      (by decide) (by decide)) hZK
  · exact (false_of_alt hKa hZK hJ hn e).elim
  · exact absurd (center_eq_bot_of_j1 h hS) hZK
  · exact concl_of_j2 hKa hI hZK hJ hS
  · exact absurd (center_eq_bot_of_j3 hSM h hS) hZK
  · exact concl_of_m12 hKa hI hZK hJ hS
  · exact concl_of_hs hKa hI hZK hJ hS
  · exact absurd (center_eq_bot_of_he h hS) hZK
  · exact absurd (center_eq_bot_of_on hSM h hS) hZK
  · exact (false_of_suz hKa hSO hJ hS).elim

end CFSG.ComponentClassification.GSThmB.Cov
