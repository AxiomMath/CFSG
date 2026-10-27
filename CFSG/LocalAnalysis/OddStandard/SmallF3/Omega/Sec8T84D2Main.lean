module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D1Lem33
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D2Dec

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E X1 X2 : Subgroup G}

theorem sec8t84d2_dec (h : Sec8T84DCtx G t E X1 X2) :
    ∃ E1 E2 : Subgroup G, Sec8T84DDec G t E X1 X2 E1 E2 := by
  have hA1 : Nonempty (↥(autIn X1 E) ≃* alternatingGroup (Fin 6)) :=
    sec8t84d2_equiv h.hX.le1 h.hX.c_le1 h.hX.quot1
  have hA2 : Nonempty (↥(autIn X2 E) ≃* alternatingGroup (Fin 6)) :=
    sec8t84d2_equiv h.hX.le2 h.hX.c_le2 h.hX.quot2
  obtain ⟨E1', E2', h33⟩ :=
    sec8t84d1_lemma33 (E := ↥E) (sec8t84d2_E_comm h.elem) (sec8t84d2_E_sq h.elem) h.elem.2
      (autIn X1 E) (autIn X2 E) (sec8t84d2_comm h.hX) hA1 hA2
  exact ⟨_, _, sec8t84d2_dec_of_dec33 h h33⟩

end CFSG.OddStandard.SmallF3.Omega
