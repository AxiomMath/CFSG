module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclTransport
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Descent
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.HSCases
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.HSConcl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Quasithin.KGC31.HS CFSG.RankThree.Native

theorem conclK_HS
    {L V MK : Subgroup (NativeSporadic.Carrier .HS)}
    (h : KConfig (NativeSporadic.Carrier .HS) L V MK) :
    ConclK (NativeSporadic.Carrier .HS) L V MK := by
  let φ : NativeSporadic.Carrier .HS ≃* G₀ := hs100Equiv
  haveI : Finite G₀ :=
    Finite.of_injective (fun x : G₀ => (x : Equiv.Perm (Fin 100))) Subtype.val_injective
  haveI : Finite (NativeSporadic.Carrier .HS) := Finite.of_injective (⇑φ) φ.injective
  have h' : KConfig G₀ (L.map φ.toMonoidHom) (V.map φ.toMonoidHom)
      (MK.map φ.toMonoidHom) := h.map_mulEquiv φ
  obtain ⟨σ, hV | hV⟩ := h'.hs_cases
  · exact ConclK.of_map_mulEquiv φ h.elemAbelian h.le_normalizer
      (h'.conclK_of_eq_map σ hV.1 hV.2 (fun MK' => conclK_hs_u16 MK'))
  · exact ConclK.of_map_mulEquiv φ h.elemAbelian h.le_normalizer
      (h'.conclK_of_eq_map σ hV.1 hV.2 (fun MK' => conclK_hs_u8 MK'))

theorem forK_HS :
    ForK (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .HS)) := by
  haveI : Finite G₀ :=
    Finite.of_injective (fun x : G₀ => (x : Equiv.Perm (Fin 100))) Subtype.val_injective
  haveI : Finite (NativeSporadic.Carrier .HS) :=
    Finite.of_injective (⇑hs100Equiv) hs100Equiv.injective
  refine forK_of_kConfig (X := NativeSporadic.Carrier .HS) ?_ ?_
  · rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_HS]
    decide
  · intro L V MK h
    exact conclK_HS h

theorem for_HS
    (h37 : CFSG.Quasithin.A37ForSQTK) (h38 : CFSG.Quasithin.A38ForSQTK)
    (h39 : CFSG.Quasithin.A39ForSQTK) :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .HS)) :=
  For.of_forK h37 h38 h39 forK_HS

end CFSG.SectionRank.QTK.Insp443

end
