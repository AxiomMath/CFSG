module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeUnitary
import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open

section Certified


theorem threeFourSolvThreeReeTwo_holds : ThreeFourSolvThreeReeTwo := by
  intro m d hd
  refine ThreeFourSolvThreeNoneAt.of_forall_lt_pRank fun K _ _ hK => ?_
  obtain ⟨e⟩ := hK
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .reeG2 m := hd
  obtain ⟨-, h3, hr⟩ := CFSG.SectionRank.smallReeModel_rank
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩)
  omega

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
