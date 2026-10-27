module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportAbs3

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

variable {H K : Type} [Group H] [Group K]

theorem HaradaFacts3.of_mulEquiv (e : H ≃* K) {E : Subgroup H} {E' : Subgroup K}
    (hE : E.map e.toMonoidHom = E') {a z b z₁ : H} {S T T' W0 : Subgroup H}
    {ι : Elem2 6 →* H} (h : HaradaFacts3 H E a z b z₁ S T T' W0 ι) :
    HaradaFacts3 K E' (e a) (e z) (e b) (e z₁) (S.map e.toMonoidHom) (T.map e.toMonoidHom)
      (T'.map e.toMonoidHom) (W0.map e.toMonoidHom) (e.toMonoidHom.comp ι) :=
  { toHaradaFacts := HaradaFacts.of_mulEquiv e hE h.toHaradaFacts
    three_conj := three_conj_map e h.three_conj
    card_C3 := card_C3_map e h.card_C3
    odd_normal := odd_normal_map e h.odd_normal
    card_tT := card_tT_map e a z z₁ h.card_tT
    perfect60 := perfect60_map e h.perfect60
    W_comm := W_comm_map e a z z₁ h.W_comm }

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
