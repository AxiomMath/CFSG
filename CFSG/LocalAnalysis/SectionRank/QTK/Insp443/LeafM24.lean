module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclTransport
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Descent
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24Cases
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24ConclOctad
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24ConclTrio
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24

theorem KConfig.conclK_m24
    {L V MK : Subgroup G₀}
    (h : KConfig G₀ L V MK) : ConclK G₀ L V MK := by
  obtain ⟨g, hcase⟩ := KConfig.m24_cases h
  rcases hcase with ⟨hV, hL⟩ | ⟨hV, hL⟩ | ⟨hV, hL⟩ | ⟨hV, hL⟩
  · exact KConfig.conclK_of_eq_map h (MulAut.conj g) hV hL (fun MK' => conclK_m24_octad MK')
  · have hperf : ⁅Ls, Ls⁆ = Ls := by
      apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      rw [Subgroup.map_commutator, ← hL, h.perfect]
    exact KConfig.conclK_of_eq_map h (MulAut.conj g) hV hL
      (fun MK' => conclK_m24_sextet hperf MK')
  · exact KConfig.conclK_of_eq_map h (MulAut.conj g) hV hL (fun MK' => conclK_m24_trio MK')
  · exact KConfig.conclK_of_eq_map h (MulAut.conj g) hV hL (fun MK' => conclK_m24_u5 MK')

theorem conclK_M24
    {L V MK : Subgroup (NativeSporadic.Carrier .M24)}
    (h : KConfig (NativeSporadic.Carrier .M24) L V MK) :
    ConclK (NativeSporadic.Carrier .M24) L V MK :=
  KConfig.conclK_m24 h

theorem forK_M24 :
    ForK (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M24)) := by
  haveI : Finite (NativeSporadic.Carrier .M24) := by
    dsimp [NativeSporadic.Carrier]
    infer_instance
  refine forK_of_kConfig ?_ (fun L V MK h => conclK_M24 h)
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M24]
  decide

theorem for_M24
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M24)) :=
  For.of_forK h37 h38 h39 forK_M24

end CFSG.SectionRank.QTK.Insp443

end
