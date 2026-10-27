module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclTransport
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Descent
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M23Cases
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M23Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Quasithin

theorem conclK_M23
    {L V MK : Subgroup (NativeSporadic.Carrier .M23)}
    (h : KConfig (NativeSporadic.Carrier .M23) L V MK) :
    ConclK (NativeSporadic.Carrier .M23) L V MK := by
  haveI : Finite (NativeSporadic.Carrier .M23) := by
    dsimp [NativeSporadic.Carrier]
    infer_instance
  obtain ⟨g, hcase⟩ := KConfig.m23_cases h
  rcases hcase with ⟨hV, hL⟩ | ⟨hV, hL⟩ | ⟨hV, hL⟩
  · exact KConfig.conclK_of_eq_map h (MulAut.conj g) hV hL (fun MK' => conclK_m23_duad MK')
  · exact KConfig.conclK_of_eq_map h (MulAut.conj g) hV hL (fun MK' => conclK_m23_w MK')
  · exact KConfig.conclK_of_eq_map h (MulAut.conj g) hV hL (fun MK' => conclK_m23_e8 MK')

theorem forK_M23 :
    ForK (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M23)) := by
  haveI : Finite (NativeSporadic.Carrier .M23) := by
    dsimp [NativeSporadic.Carrier]
    infer_instance
  refine forK_of_kConfig ?_ (fun L V MK h => conclK_M23 h)
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M23]
  decide

theorem for_M23
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M23)) :=
  For.of_forK h37 h38 h39 forK_M23

end CFSG.SectionRank.QTK.Insp443

end
