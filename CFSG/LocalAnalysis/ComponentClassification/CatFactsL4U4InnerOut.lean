module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerCase
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutU

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank

theorem cfRow516InnerOut : CFRow516InnerOut := by
  intro H _ _ h hrow hin u v
  obtain ⟨-, p, f, hp, hp2, hf, -, hL | hU⟩ := inner_structure h hrow hin
  · obtain ⟨hq, F, _, _, hF, ⟨e⟩⟩ := hL
    set e' : OddBar h.K ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F :=
      e.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
        (QuotientGroup.quotientMulEquivOfEq
          (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 F).symm))
    exact commutator_mem_range_conj_of_mulEquiv e'
      (fun u v => LinearOut.out_comm_projectiveSL_four (by rw [hF]; exact hq) u v) u v
  · obtain ⟨hq, K', _, hUF, ⟨e⟩⟩ := hU
    exact commutator_mem_range_conj_of_mulEquiv e
      (fun u v => UnitaryOut.out_comm_statedSU_four hUF hp2 hq u v) u v

end CFSG.ComponentClassification.CatFactsL4U4
