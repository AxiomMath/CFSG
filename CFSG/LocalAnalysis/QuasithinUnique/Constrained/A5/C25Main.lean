module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Link
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Rep
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Y2

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

theorem comp25Component_of
    (hC54 : LemmaC54_3_s2) (h567 : Lemma245_C56_7)
    (h36 : Vol2Native.A36ForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hP1 : CompChi0Block)
    (hP2 : NoProperA5Block) : Comp25Component := by
  intro G _ _ T M H S L cfg x hxT _ hxU hB
  have S' := C25.setting_of_A5 hC54 h567 h37 h39 hP1 hP2 cfg hxT hxU hB
  obtain ⟨y, hyC, hy3, hyL⟩ := C25.exists_order_three_cent hC54 h567 cfg
  obtain ⟨K, hK, hLK⟩ := C25.exists_cComp_of_order_three h36 h37 h38 h39 S'
    (Subgroup.centralizer_le_normalizer _ hyC) hy3 hyL
  have hn := C25.normal_of_rankOne C25.rankOneLocalSolvable h37 h38 S' hK hLK
  have hnc := C25.not_charTwo S' hK hLK hn
  obtain ⟨TI, z, hTI, hzTI, hzc, hz2, hinv⟩ := C25.exists_inv_of_A5 cfg hB
  have hq := C25.isQuasisimple_of_inv h36 S' hK hLK hn hnc hTI hzTI hzc hz2 hinv
  exact ⟨K, C25.isComponentIn_of_mem_cComp hK hq, hLK, hn⟩

end CFSG.QuasithinUnique.A5
