module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.RankIndex
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcTits
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 TauCeti

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

section Certs


theorem false_of_tits (h : E27Config X K R T z) (hz : z ∈ K) {hv : LieTypeIndex.tits.Valid}
    (e : Nonempty (↥K ≃* (CFSGIndex.lie ⟨.tits, hv⟩).Group)) : False := by
  obtain ⟨e⟩ := e
  have hm := CFSG.HardMathSupport.Timmesfeld.Tables.Census.reeTitsModel_tits_of_equiv e
  obtain ⟨F, _, _, _, hF, ⟨e'⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hm
  exact false_of_elemAbelian_card_lt h hz e' fun E hE =>
    CFSG.StandardType.TableBExcSmallRest.card_lt_of_isElemAbelian_commutator_reeFixed hF hE

end Certs

end CFSG.HardMathSupport.Malle.E27Lie
