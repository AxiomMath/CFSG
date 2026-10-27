module

public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerIndex
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerTrans
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerDiag
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerTorusLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerTorusUni
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerD4
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrStableAlternating

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)


theorem kFactTwoGenInner_of_d4 (hD4 : D4PGood) : KFactTwoGenInner := by
  intro Y _ _ L hLcomp hcat p hp hp5 hcases x hx hxp
  have hq : CFSG.Open.IsQuasisimple ↥L := hLcomp.2.2
  have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  have hnabS : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hnabL : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabS
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) b
    exact ⟨a', b', fun h' => hab (by rw [← map_mul, ← map_mul, h'])⟩
  have e₀ : Subgroup.center ↥L = ⊥ → Nonempty (↥L ⧸ Subgroup.center ↥L ≃* ↥L) := fun hZ =>
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩
  have hgood : PGoodOut p (↥L ⧸ Subgroup.center ↥L) := by
    rcases hcases with h1 | h2 | ⟨m, hm | hm⟩ | ⟨h4, T, hT, hcop⟩
    · have hpT : ¬ p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := fun hd =>
        h1 (hd.trans (Subgroup.card_quotient_dvd_card _))
      exact pGoodOut_of_catalogGroup hnabS hcat hp hp5
        (fun hm => not_dvd_gcd_psl_of_not_dvd_card hp hp5 hm hpT)
        (fun hm => not_dvd_gcd_psu_of_not_dvd_card hp hp5 hm hpT) hD4
    · obtain ⟨e⟩ := e₀ (CFSG.AGLEmbedding.center_eq_bot_of_isOrthogonalTwo hperf hnabL h2)
      exact pGoodOut_of_isOrthogonalTwo hp hp5
        (CFSG.AGLEmbedding.IsOrthogonalTwo.of_mulEquiv e h2) hD4
    · obtain ⟨φ⟩ := hm
      obtain ⟨e⟩ := e₀ (CFSG.AGLEmbedding.center_eq_bot_of_mulEquiv_alternating hnabL φ)
      exact pGoodOut_of_alternating
        (CFSG.ComponentClassification.UnbalancedCorr.five_le_of_mulEquiv_alternatingGroup hnabS
          (e.trans φ)) hp hp5 (e.trans φ)
    · obtain ⟨φ⟩ := hm
      exact pGoodOut_of_alternating
        (CFSG.ComponentClassification.UnbalancedCorr.five_le_of_mulEquiv_alternatingGroup hnabS φ)
        hp hp5 φ
    · refine pGoodOut_of_isClassicalTwoOrG2 hp hp5 h4 (fun {n f} hm hdvd => ?_)
        (fun {n f} hm hdvd => ?_) hD4
      · exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hcop
          (torusLin Y L T n f p hp hp5 hq hm hdvd hT))
      · exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hcop
          (torusUni Y L T n f p hp hp5 hq hm hdvd hT))
  exact mem_sup_centralizer_of_pGoodOut L hq hp (by omega) hgood hx hxp

theorem kFactTwoGenInner : KFactTwoGenInner := kFactTwoGenInner_of_d4 d4PGood

end CFSG.AGLEmbedding.TwoGenInner
