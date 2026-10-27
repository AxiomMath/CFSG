module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenOneEightCover
import CFSG.HardMathSupport.Cooperstein.Coordinator.Reduction
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541EvenExcl
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.Quasithin.Vol2.Ch11SecD557NatA

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin CFSG.QuasithinUnique.Setup
  CFSG.HardMathSupport.Cooperstein.Coordinator

open scoped MatrixGroups

namespace TenOneEight

attribute [local instance] blockVCommGroup

theorem nonempty_barM_mulEquiv_SL3
    {G : Type} [Group G] [Finite G]
    {X S L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) {n : ℕ}
    (hn : IsLieOver (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) (.A 2) 2 n) :
    Nonempty (↥(barM X L) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
  classical
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hq : CFSG.IsQuasisimple ↥(barM X L) := isQuasisimple_of_open' hL.component.2.2
  have hodd : Odd (Nat.card (Subgroup.center ↥(barM X L))) := by
    rw [CFSG.HardMathSupport.Cooperstein.Proving.card_center_eq_of_mulEquiv
      (CFSG.HardMathSupport.Cooperstein.Proving.barMEquiv hL.le (le_sup_left : L ≤ L ⊔ S)
        (inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL)).symm]
    exact CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.odd_card_center_barM_sup
      (asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL) hSL
  obtain ⟨⟨d, hv⟩, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := hn
  simp only at hd
  subst hd
  have hn1 : 1 ≤ n := hqe ▸ q.exponent_pos
  have hmodel : StatedClassicalModel (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) .PSL 3 2 n := by
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rwa [hqp, hqe] at h
  obtain ⟨F, iF, iFin, φ, hFcard, hcov⟩ := X7Sec.exists_cover_of_model hq.1 hodd hn1 hmodel
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ n := by rw [Fintype.card_eq_nat_card]; exact hFcard
  by_cases hinj : Function.Injective φ
  · have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have hcard : Fintype.card F = Fintype.card (GaloisField 2 n) := by
      rw [hF, ← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
    exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hcov.surjective⟩).symm.trans
      (CFSG.Quasithin.Vol2.Ch11.SecD.slMapEquiv (FiniteField.ringEquivOfCardEq hcard))⟩
  exfalso
  obtain ⟨hc, hev⟩ := center_eq_bot_and_even_of_not_injective hF hcov hinj
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hev
    omega
  obtain ⟨h, hs, hk⟩ := exists_central_factor_autOn hA hL hSL
  have hinjh : Function.Injective h := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hk.trans hc.le
  let eh : ↥(barM X L) ≃* ↥(autOn L (blockV S L)) := MulEquiv.ofBijective h ⟨hinjh, hs⟩
  have hcs : Subgroup.center ↥(autOn L (blockV S L)) = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [CFSG.HardMathSupport.Cooperstein.Proving.card_center_eq_of_mulEquiv eh, hc,
      Subgroup.card_bot]
  have hV2 : ∀ v : ↥(blockV S L), v ^ 2 = 1 := fun v =>
    Subtype.ext ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _).2 _ v.2)
  obtain ⟨hLF, hLq, hO2, -⟩ := ffHyp_autOn hA hL hSL hX
  obtain ⟨W, _, _, LW, E, hW, hLWq, hirr, ⟨eW⟩, hEN, hE1, hEel, hEq, hoff⟩ :=
    exists_irrFFOffender_of_center_eq_bot hV2 hLF hLq hO2 hcs (isFFModule_autOn_blockV hA hL hSL)
  have hcW : Subgroup.center ↥LW = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [CFSG.HardMathSupport.Cooperstein.Proving.card_center_eq_of_mulEquiv (eh.trans eW),
      hc, Subgroup.card_bot]
  let q₁ : ↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* ↥(barM X L) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  let q₂ : ↥LW ⧸ Subgroup.center ↥LW ≃* ↥LW :=
    (QuotientGroup.quotientMulEquivOfEq hcW).trans QuotientGroup.quotientBot
  have hmodelW : StatedClassicalModel (↥LW ⧸ Subgroup.center ↥LW) .PSL 3 2 n :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ((q₁.trans (eh.trans eW)).trans q₂.symm)
      hmodel
  exact absurd hoff (not_le.2 (CFSG.LocalAnalysis.RankThreeUC.S15.evenExclusion hev hn2 W hW LW E
    hirr hLWq.1 hcW hmodelW hEN hE1 hEel hEq))

end TenOneEight

theorem kFactTenOneEight_holds :
    KFactTenOneEight :=
  fun _ _ _ _ _ _ hB _ _ hn => TenOneEight.nonempty_barM_mulEquiv_SL3 hB.1 hB.2.1 hB.2.2.1 hn

end CFSG.LocalAnalysis.RankThreeTheoremC
