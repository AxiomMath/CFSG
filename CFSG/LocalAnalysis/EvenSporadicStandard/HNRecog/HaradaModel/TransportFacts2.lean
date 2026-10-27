module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportAbs2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog.TwoHSData

variable {H K : Type} [Group H] [Group K]

theorem HaradaFacts2.of_mulEquiv (e : H ≃* K) {E : Subgroup H} {E' : Subgroup K}
    (hE : E.map e.toMonoidHom = E') {a z b z₁ : H} {S T T' W0 : Subgroup H}
    {ι : Elem2 6 →* H} {zv : V6} {R0 F : Subgroup H}
    (h : HaradaFacts2 H E a z b z₁ S T T' W0 ι zv R0 F) :
    HaradaFacts2 K E' (e a) (e z) (e b) (e z₁) (S.map e.toMonoidHom) (T.map e.toMonoidHom)
      (T'.map e.toMonoidHom) (W0.map e.toMonoidHom) (e.toMonoidHom.comp ι) zv
      (R0.map e.toMonoidHom) (F.map e.toMonoidHom) := by
  have hcen : (centralizer ({z} : Set H)).map e.toMonoidHom = centralizer ({e z} : Set K) :=
    map_centralizer_singleton e z
  exact
    { toHaradaFacts := HaradaFacts.of_mulEquiv e hE h.toHaradaFacts
      ι_zv := by rw [MonoidHom.comp_apply, h.ι_zv]; rfl
      lam_zv := h.lam_zv
      qm_zv := h.qm_zv
      card_R0 := (card_map_mulEquiv e R0).trans h.card_R0
      R0_le_centralizer := map_le_centralizer_singleton e h.R0_le_centralizer
      R0_le_normalizer := map_le_normalizer_range e ι h.R0_le_normalizer
      R0_normal := by
        rw [← hcen]
        exact normal_map e h.R0_normal
      R0_max := by
        rw [← hcen]
        exact max_map e h.R0_max
      R0_sq := sq_map e h.R0_sq
      R0_comm := comm_map e h.R0_comm
      R0_inter := fun v => by
        rw [MonoidHom.comp_apply]
        exact (mem_map_iff e R0 _).trans (h.R0_inter v)
      R0_eichler := eichler_map e ι h.R0_eichler
      R0_surj := surj_map e ι h.R0_surj
      R0_faith := by
        rw [← hcen]
        exact faith_map e h.R0_faith
      F_le_centralizer := map_le_centralizer_singleton e h.F_le_centralizer
      F_le_normalizer := map_le_normalizer_range e ι h.F_le_normalizer
      F_iso := ⟨(mapSubgroupMulEquiv e F).symm.trans h.F_iso.some⟩ }

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
