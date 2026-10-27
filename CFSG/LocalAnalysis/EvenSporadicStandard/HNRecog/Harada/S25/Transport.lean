module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.Joint
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.Transport27
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportFacts3

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

theorem HaradaFactsAll.of_mulEquiv {H K : Type} [Group H] [Group K] (e : H ≃* K)
    {E : Subgroup H} {E' : Subgroup K} (hE : E.map e.toMonoidHom = E') {a z b z₁ : H}
    {S T T' W0 : Subgroup H} {ι : Elem2 6 →* H} {zv : V6} {R0 F : Subgroup H}
    (h : HaradaFactsAll H E a z b z₁ S T T' W0 ι zv R0 F) :
    HaradaFactsAll K E' (e a) (e z) (e b) (e z₁) (S.map e.toMonoidHom) (T.map e.toMonoidHom)
      (T'.map e.toMonoidHom) (W0.map e.toMonoidHom) (e.toMonoidHom.comp ι) zv
      (R0.map e.toMonoidHom) (F.map e.toMonoidHom) :=
  have h3 := HaradaModel.HaradaFacts3.of_mulEquiv e hE h.toHaradaFacts3
  { toHaradaFacts27 := HaradaFacts27.of_mulEquiv e hE h.toHaradaFacts27
    three_conj := h3.three_conj
    card_C3 := h3.card_C3
    odd_normal := h3.odd_normal
    card_tT := h3.card_tT
    perfect60 := h3.perfect60
    W_comm := h3.W_comm
    splus := h.splus.of_mulEquiv e }

end CFSG.EvenSporadicStandard.HNRecog.Harada.S25
