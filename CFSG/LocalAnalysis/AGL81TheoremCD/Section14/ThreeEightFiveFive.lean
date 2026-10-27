module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Assembly
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTenGood
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.HeisGood
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFiveOrder

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFive

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem card_outer_j4_group :
    Nat.card (Outer (TauCeti.CFSGIndex.sporadic .J4).Group) = 1 := by
  obtain ⟨eJ⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  let eC : Blueprint.NativeSporadic.Carrier .J4 ≃* Blueprint.NativeSporadic.J4 :=
    MulEquiv.refl _
  exact (Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (eC.trans eJ)).toEquiv).symm.trans CFSG.AGLEmbedding.card_outer_J4


theorem good_of_nineFourListGroup_of_five_le {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) {X : Type}
    [Group X] [Finite X] (hO : CFSG.pPrimeCore q X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup X))
    (hF : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q
      ↥(CFSG.generalizedFitting X))
    {N : Subgroup X} (hN : IsStronglyPEmbedded q N) :
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Good q N := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hKs, i, hi, ⟨e⟩⟩ := hF
  obtain ⟨-, -, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hq hO hN
  haveI : (CFSG.generalizedFitting X).Normal := hKn
  haveI : IsSimpleGroup ↥(CFSG.generalizedFitting X) := hKs
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n _ =>
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · omega
    · exact SEFive.good_altTen hO hN e
  | sporadic s =>
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    ·
      have h9 : 9 ∣ Nat.card ↥(CFSG.generalizedFitting X) := by
        rw [Nat.card_congr e.toEquiv, card_sporadic_McL]
        norm_num
      exact SEFive.good_of_heis (Or.inl rfl) CFSG.AGLEmbeddingD2.d2HeisLocalAt_mcl hO hN e
        (h9.trans (Subgroup.card_subgroup_dvd_card _)) (fun h => absurd h (by norm_num))
    ·
      have hXJ : Nat.card X = 86775571046077562880 :=
        (SEFive.card_eq_of_mulEquiv_of_card_outer_eq_one hKC e card_outer_j4_group).trans
          card_sporadic_J4
      exact SEFive.good_of_heis (Or.inr rfl)
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4 hO hN e
        (by rw [hXJ]; norm_num) (fun _ => by rw [hXJ]; norm_num)
  | lie d =>
    rcases hi with ⟨qp, hqp, hq2, hd⟩ | ⟨qp, hqp, hd⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hd | hd⟩
    ·
      obtain ⟨f⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
        (p := q) (n := qp.exponent) (d := d) ⟨qp, hd, hqp, rfl⟩
      exact SEFive.good_psl2GF (p := q) (n := qp.exponent) (by omega) (by omega) hO hN
        (e.trans f)
    ·
      exact SEFive.good_unitary (p := q) (d := d) ⟨qp, hqp, hd⟩ hO hN e
    · omega
    · omega
    ·
      obtain ⟨d1, hv⟩ := d
      change d1 = .suzuki 2 at hd
      subst hd
      exact SEFive.good_sz32 hO h2 hN ⟨hv, ⟨e⟩⟩
    ·
      obtain ⟨d1, hv⟩ := d
      change d1 = .tits at hd
      subst hd
      exact SEFive.good_tits hO hN ⟨⟨.tits, hv⟩, rfl, ⟨e⟩⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFive
