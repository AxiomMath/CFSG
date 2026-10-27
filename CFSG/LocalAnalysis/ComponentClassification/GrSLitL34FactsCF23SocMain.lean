module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Socle
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocOdd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocEven
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocSpor
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocHS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocL316
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocLin

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

theorem cf23L34Socle_holds
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hSuzO : SolMax.SuzOuterComponentsInput)
    (hONO : SolMax.ONOuterComponentsInput) : CF23L34Socle := by
  intro G _ _ N hN hS hC hR α J hα hJN hJC hJ hL
  have h : Soc.Hyp N α J := ⟨hS, hC, hα, hJN, hJC, hJ, hL⟩
  rcases hR with ⟨p, f, hp, hp2, -, -, hm⟩ | ⟨p, f, hp, hp2, -, hm⟩ | ⟨m, -, hm⟩ | hm | hm | hm |
      hm | hm | hm | hm | ⟨n, hn, ⟨θ⟩⟩ | hs | hs | hs | hs | hs | hs | hs | hs
  · exact (h.false_of_lieModel_odd hGLS hm hp hp2).elim
  · rcases hm with hm | hm | hm | hm | hm | hm | hm <;>
      exact (h.false_of_lieModel_odd hGLS hm hp hp2).elim
  · exact (h.false_of_lieModel_odd hGLS hm Nat.prime_three (by decide)).elim
  · exact (h.false_of_psl_two_sixteen hm).elim
  · exact (h.false_of_psl_three_four hm).elim
  · exact (h.false_of_psu_three_four hm).elim
  · exact (h.false_of_psp_four_four hm).elim
  · exact (h.false_of_psl_five_two hm).elim
  · exact (h.false_of_psu_five_two hm).elim
  · obtain ⟨K, _, _, φ, ρ, c, σ, hK, hinj, hρW, hσ, hρa⟩ := h.field_form hm
    exact Or.inr ⟨hm, Soc.coset_conj h.ne_one hK φ ρ hinj hρW c σ hσ hρa⟩
  · exact (h.false_of_alternating (by omega) θ).elim
  · exact (h.false_of_J1 hs).elim
  · exact (h.false_of_J2 hs).elim
  · exact (h.false_of_J3 hs).elim
  · exact (h.false_of_M12 hs).elim
  · exact (h.false_of_HS hs).elim
  · exact Or.inl (Or.inl hs)
  · exact Or.inl (Or.inr ⟨h.mem_of_ON hONO hs, Or.inr hs⟩)
  · exact Or.inl (Or.inr ⟨h.mem_of_suz hSuzO hs, Or.inl hs⟩)

end CFSG.ComponentClassification.GSThmB
