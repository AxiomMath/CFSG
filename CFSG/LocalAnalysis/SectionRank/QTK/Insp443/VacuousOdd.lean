module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Vacuous
public import CFSG.Quasithin.Vol2.KGFactC31M12
public import CFSG.Quasithin.Vol2.KGFactC31J2

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint

theorem Hyp.false_of_noOddAct {G : Type} [Group G] [Finite G] {T M L B Tp VB K : Subgroup G}
    (h : Hyp G T M L B Tp VB K)
    (hS : CFSG.Quasithin.KGC31.NoOddAct (↥K ⧸ Subgroup.center ↥K)) : False := by
  obtain ⟨E, Y, hE, h8, hYperf, hFnorm, hEY, hEeq⟩ := h.exists_images
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h8
    omega
  exact CFSG.Quasithin.KGC31.false_of_noOddAct
    (CFSG.Quasithin.KGC31.noOddAct_of_mulEquiv Subgroup.topEquiv hS)
    le_top hYperf hEY hEne hE hEeq.symm

theorem For.of_noOddAct {P : (S : Type) → [Group S] → Prop}
    (hP : ∀ (S : Type) [Group S] [Finite S], P S → CFSG.Quasithin.KGC31.NoOddAct S) : For P := by
  intro G _ _ T M L B Tp VB K hH hPK
  exact (Hyp.false_of_noOddAct hH (hP _ hPK)).elim

theorem for_M12 :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M12)) := by
  refine For.of_noOddAct (fun S _ _ hP => ?_)
  obtain ⟨e⟩ := hP
  exact CFSG.Quasithin.KGC31.noOddAct_of_mulEquiv e CFSG.Quasithin.KGC31.noOddAct_m12

theorem for_J2 :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .J2)) := by
  refine For.of_noOddAct (fun S _ _ hP => ?_)
  obtain ⟨e⟩ := hP
  exact CFSG.Quasithin.KGC31.noOddAct_of_mulEquiv e CFSG.Quasithin.KGC31.noOddAct_j2

end CFSG.SectionRank.QTK.Insp443

end
