module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedClose3Block
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedClose3Solv
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal D1Escape D1PhaseThree Asc81bEightFive Asc81bNineThree
  D1NoXBlock IsWeakSBlock glbPrimeCore_coprime)

variable {G : Type} [Group G] [Finite G]

@[expose] def D1ConstrainedWeakBlockSolv3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H : Subgroup G, D1Extremal p P M H (P : Subgroup G) →
      ∀ (_ : Fact p.Prime) (z : G), D1CentralizerInput3 p P M z →
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) = ⊥ →
      ∀ (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
        (E C : Subgroup (ReducedCentralizer p z)) (_ : E.Normal)
        (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)),
        D1ConstrainedReducedData3 p P M z Pbar zbar →
        ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e →
      HasPrimeConstraint (G := H) p → D1PhaseThree p P M H (P : Subgroup G) →
      z ∈ (P : Subgroup G) → Subgroup.centralizer ({z} : Set G) ≤ H →
      (∀ K : Subgroup G, GLBIsMaxTwoLocal K → (P : Subgroup G) ≤ K → ¬ K ≤ M → K = H) →
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ H →
      ∀ T : Subgroup G, T ≤ GLBPrimeCore p H → IsPGroup 2 T →
        ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index →
        (P : Subgroup G) ≤ Subgroup.normalizer (T : Set G) → pCoreOf 2 H ≤ T →
        (∀ U : Subgroup G, U ≤ T → U ≠ ⊥ → (U.subgroupOf T).Characteristic →
          Subgroup.normalizer (U : Set G) ≤ H) →
        (p = 3 → Group.IsSolvable (H ⧸ primeComplementCore (G := H) p)) →
        ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
          (p = 3 → Group.IsSolvable ↥(Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) ⊓
            L)) → False

theorem d1ConstrainedWeakBlockResidue3_of_solv (hK : KFactBlockPerfectCoreThree)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (h : D1ConstrainedWeakBlockSolv3 G) : D1ConstrainedWeakBlockResidue3 G := by
  intro hS p hp P M hM H hext hfact z hz hlayer Pbar zbar E C hEn e hdata hstr hcon hph hzP hCH
    huniq hNH T hTN hT2 hTidx hPT hST hchar L hL
  have hsolvH : p = 3 → Group.IsSolvable (H ⧸ primeComplementCore (G := H) p) := by
    intro hp3
    subst hp3
    exact isSolvable_primeCore_quotient_three P hext.sylow_le hext.weakCore_le
      hext.toD1Escape.three_le_pRank_inf hext.not_le hcon
  refine h hS p hp P M hM H hext hfact z hz hlayer Pbar zbar E C hEn e hdata hstr hcon hph hzP hCH
    huniq hNH T hTN hT2 hTidx hPT hST hchar hsolvH L hL fun hp3 => ?_
  have hsolv := hsolvH hp3
  subst hp3
  have hN : Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) = H :=
    hext.toD1Escape.normalizer_twoCore_H
  have hyps : BlockL28Hyps M (pCoreOf 2 H) L :=
    ⟨hph.isKGroup.1, hph.asc81bHyp, hL, hph.nineThree h93 hL,
      (hph.nineThree_not_one h85 hD2 hL).1, hph.not_isSylowTwoOf_inf h85 hD2 hL⟩
  refine isSolvable_normalizer_inf_of_blockHyps hK hyps fun D hD hDD h3 => ?_
  have hDH : D ≤ H := fun x hx => by rw [← hN]; exact (hD hx).1
  have hDHM : D ≤ H ⊓ M := le_inf hDH (hD.trans (inf_le_right.trans hL.le))
  have hle : D ≤ GLBPrimeCore 3 H :=
    CFSG.AGLEmbedding.le_glbPrimeCore_of_perfect (M := M) inferInstance hDHM hDD
  have hcop : Nat.Coprime 3 (Nat.card (GLBPrimeCore 3 H)) := glbPrimeCore_coprime 3 H
  have hdvd : Nat.card D ∣ Nat.card (GLBPrimeCore 3 H) := Subgroup.card_dvd_of_le hle
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right hdvd hcop) h3
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
