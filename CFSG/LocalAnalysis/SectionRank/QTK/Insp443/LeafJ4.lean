module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.J4M3
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.J4Branches
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfTransport
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.TwoLocalRed
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclTransport
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Descent
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4A
public import CFSG.Milestones.ASVolI.C31.J4KWHolds
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows

public section

namespace CFSG.SectionRank.QTK.Insp443.J4

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.J4 CFSG.Quasithin.KGC31.J4M4 CFSG.Quasithin.J4Loc

theorem forK_of_conclK {X Y : Type} [Group X] [Finite X] [Group Y] (eXY : X ≃* Y)
    (hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) ∣ 2)
    (hX : ∀ L V MK : Subgroup X, KConf X L V MK → ConclK X L V MK) :
    ForK (fun S _ => Nonempty (S ≃* Y)) := by
  intro K _ _ L V MK hK hP
  obtain ⟨e⟩ := hP
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_hopfMultiplier hK.quasisimple hK.odd_card_center e hM
  let eK : K ≃* X :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans
      (e.trans eXY.symm)
  exact ConclK.of_map_mulEquiv eK hK.elemAbelian hK.le_normalizer (hX _ _ _ (hK.map_mulEquiv eK))

section Main


theorem pCoreOf_maxLoc_ne_bot (i : Fin 4) : pCoreOf 2 (maxLoc i) ≠ ⊥ := by
  have hF := j4Facts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ∀ {X P : Subgroup G₀}, P ≤ pCoreOf 2 X → 1 < Nat.card P → pCoreOf 2 X ≠ ⊥ :=
    fun {X P} hP h1 hb => by
      rw [hb, le_bot_iff] at hP
      rw [hP, Subgroup.card_bot] at h1
      exact lt_irrefl _ h1
  fin_cases i
  · have F := hFacts iso_id
    rw [Subgroup.map_id, Subgroup.map_id, Subgroup.map_id] at F
    exact hne (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 F.EH F.NE.ge F.pGroup)
      (by rw [F.card]; norm_num)
  · show pCoreOf 2 CFSG.Quasithin.J4M2.M2 ≠ ⊥
    exact hne (le_of_eq CFSG.Quasithin.J4M2Core.pCoreOf_M2_eq.symm)
      (by rw [CFSG.Quasithin.J4M2.card_Qgrp hF.mat]; norm_num)
  · show pCoreOf 2 CFSG.Quasithin.J4Fam.M3 ≠ ⊥
    exact hne (le_of_eq CFSG.Quasithin.J4M3.pCoreOf_M3_eq.symm)
      (by rw [CFSG.Quasithin.J4M3.card_Q]; norm_num)
  · show pCoreOf 2 CFSG.Quasithin.KGJ4.M4 ≠ ⊥
    exact hne (le_of_eq (pCoreOf_M4 hF.mat chkF_true CFSG.Quasithin.J4M4Card.card_M4).symm)
      (by rw [card_F4]; norm_num)

theorem exists_conj_maxLoc {L V MK : Subgroup G₀} (h : KConfig G₀ L V MK) :
    ∃ i : Fin 4, ∃ g : G₀, L.map (MulAut.conj g).toMonoidHom ≤ maxLoc i ∧
      maxLoc i ≤ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G₀) : Set G₀) := by
  obtain ⟨i, g, hN⟩ := kw1 CFSG.ASVolI.burnsideJ4KW_twoLocals_holds iso_id
    h.elemAbelian.isPGroup h.ne_bot
  rw [Subgroup.map_id] at hN
  obtain ⟨hLY, hYL⟩ := h.le_and_normalizer_of_inner
    (fun σ => CFSG.Quasithin.H13.Ch4.G443J4.all_inner_of_isSporadic_j4 isSporadic_J σ) hN
    (pCoreOf_map_conj_ne_bot g (pCoreOf_maxLoc_ne_bot i))
  exact ⟨i, g⁻¹, le_and_normalizer_of_map_conj g hLY hYL⟩

theorem conclK_J {L V MK : Subgroup G₀} (h : KConf G₀ L V MK) : ConclK G₀ L V MK := by
  obtain ⟨i, g, hLY, hYL⟩ := exists_conj_maxLoc h.kConfig
  have h' := h.map_mulEquiv (MulAut.conj g)
  have hne : L.map (MulAut.conj g).toMonoidHom ≠ ⊥ := fun hb => h'.ne_bot (by
    rw [eq_bot_iff]
    exact h'.le_pCoreOf.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (le_of_eq hb)))
  have hc : ConclK G₀ (L.map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom)
      (MK.map (MulAut.conj g).toMonoidHom) := by
    fin_cases i
    · exact conclK_of_le_Hj hLY hYL h'.perfect hne
    · exact (false_of_le_M2 hLY hYL h'.perfect h'.le_pCoreOf h'.pCoreOf_le h'.le_normalizer
        h'.eq_commutator h'.ne_bot).elim
    · exact conclK_of_le_M3 h' hLY hYL
    · exact conclK_of_le_M4 hLY hYL h'.perfect hne
  exact ConclK.of_map_mulEquiv (MulAut.conj g) h.elemAbelian h.le_normalizer hc

end Main

theorem forK_J4 :
    ForK (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .J4)) := by
  obtain ⟨eXY⟩ : IsSporadic .J4 G₀ := isSporadic_J
  refine forK_of_conclK eXY ?_ (fun L V MK h => conclK_J h)
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_J4]
  decide


theorem for_J4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .J4)) :=
  For.of_forK h37 h38 h39 forK_J4

end CFSG.SectionRank.QTK.Insp443.J4
