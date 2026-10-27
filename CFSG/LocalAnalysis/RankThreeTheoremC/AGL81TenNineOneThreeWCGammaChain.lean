module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaAlt6
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaAlt9
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaM11
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaM12
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaL33
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaL34
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaL2
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaU42
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaSp62
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaJ3
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaSp48
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaG28
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactNineFourSylowIrredProof
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Cat
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open TenNineOneThree (IsWClosedIn GammaZeroIn)
open Subgroup

@[expose] def KFactTenNineWCGammaRk : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal], NineThreeListGroup 3 K →
    Open.pRank 3 K ≤ 3 →
    ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
      (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
      GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
      IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y →
      IsCaseIThreeSimple K ∨ IsCaseIThreeProd K ∨
        (IsCaseIThreeG28 K ∧ ∀ A' : Subgroup (MulAut.conjNormal (H := K)).range,
          Nat.card A' = 3 →
          IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A' Y → A' = A)

open TenNineOneThree in
theorem kFactTenNineWCGammaRk_of
    (hGc : KFactG28SylowCenter) : KFactTenNineWCGammaRk := by
  intro B _ _ K _ hl hrk S A Y hA3 hY hwc
  have hrk' : Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  rcases hl with ⟨i, hi, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · cases i with
    | cyclic p hp => exact hi.elim
    | alternating n hn =>
      rcases hi with ⟨-, rfl | rfl⟩ | ⟨h, -⟩
      · exact (kFactTenNineWCGammaAlt6 B K ⟨e⟩ S A Y hA3 hY hwc).elim
      · exact (kFactTenNineWCGammaAlt9 B K ⟨e⟩ S A Y hA3 hY hwc).elim
      · exact absurd h (by norm_num)
    | sporadic s =>
      rcases hi with ⟨-, rfl | rfl | rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact (kFactTenNineWCGammaM11 B K ⟨e⟩ S A Y hA3 hY hwc).elim
      · obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
        exact (kFactTenNineWCGammaM12 B K ⟨e.trans eC.symm⟩ S A Y hA3 hY hwc).elim
      · obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
        exact (kFactTenNineWCGammaJ3 B K
          ⟨e.trans (ψ.symm.trans CFSG.Sporadic.Schreier.j3PermEquiv)⟩ S A Y hA3 hY hwc).elim
      all_goals exact absurd h (by norm_num)
    | lie d =>
      change IsNineThreeLieIndex 3 d at hi
      rcases hi with ⟨q, hqp, hqe, hd1⟩ | ⟨q, hqp, hd1⟩ | hsp | ⟨q, hqp, hqe, hd1⟩ |
        ⟨-, m, hd1⟩ | ⟨-, (⟨q, hqp, hqe, hd1 | hd1 | hd1⟩ | ⟨q, hqp, hqe, hd1⟩ |
          ⟨q, hqp, hqe, hd1⟩ | hd1)⟩ | ⟨h, -⟩
      · obtain ⟨F, _, _, _, h9, he⟩ := L2.exists_equiv_psl2 d ⟨q, hqp, hqe, hd1⟩ e
        exact (L2.kFactTenNineWCGammaL2 B K F h9 he S A Y hA3 hY hwc).elim
      · by_cases hqe : 2 ≤ q.exponent
        · have := NineFourIrred.four_le_pRank_unitary (by norm_num) hqp hqe hd1 e
          omega
        · left
          exact ⟨d, Or.inr ⟨q, hqp, by have := q.exponent_pos; omega, hd1⟩, ⟨e⟩⟩
      · exact (kFactTenNineWCGammaU42 B K (nonempty_V0_of_isSpFourIndex d hsp e) S A Y hA3 hY
          hwc).elim
      · exact (kFactTenNineWCGammaL33 B K (nonempty_equiv_sl33 d ⟨q, hqp, hqe, hd1⟩ e) S A Y hA3
          hY hwc).elim
      · have := four_le_pRank_ree hd1 e
        omega
      · left
        exact ⟨d, Or.inl ⟨q, hqp, hqe, hd1⟩, ⟨e⟩⟩
      · right; right
        exact ⟨⟨d, ⟨q, hqp, hqe, hd1⟩, ⟨e⟩⟩, fun A' hA' hwc' =>
          kFactTenNineWCGammaG28Uniq_of hGc B K ⟨d, ⟨q, hqp, hqe, hd1⟩, ⟨e⟩⟩ S A Y hA3 hY.1 hwc
            A' hA' hwc'⟩
      · exact (kFactTenNineWCGammaSp48 B K ⟨d, ⟨q, hqp, hqe, hd1⟩, ⟨e⟩⟩ S A Y hA3 hY hwc).elim
      · obtain ⟨d1, hv⟩ := d
        subst hd1
        exact (kFactTenNineWCGammaL34 B K ⟨q, hqp, hqe, hv, ⟨e⟩⟩ S A Y hA3 hY hwc).elim
      · exact (kFactTenNineWCGammaSp62 B K (nonempty_H6_of_B3 d ⟨q, hqp, hqe, hd1⟩ e) S A Y hA3
          hY hwc).elim
      · obtain ⟨d1, hv⟩ := d
        subst hd1
        obtain ⟨eT⟩ :=
          CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.nonempty_mulEquiv_titsD_cat hv
        exact (kFactTenNineWCGammaTits B K ⟨e.trans eT⟩ S A Y hA3 hY hwc).elim
      · exact absurd h (by norm_num)
  · rcases hd with ⟨-, hq⟩ | ⟨h, -⟩
    · right; left
      exact ⟨d, hq, ⟨e⟩⟩
    · exact absurd h (by norm_num)

variable (G : Type) [Group G] [Finite G]

@[expose] noncomputable def agl81YHat (M H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) [K.Normal] :
    Subgroup (MulAut.conjNormal (H := K)).range :=
  (((M.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3))).map
    (MulAut.conjNormal (H := K))).subgroupOf (MulAut.conjNormal (H := K)).range

variable {G}

end CFSG.LocalAnalysis.RankThreeTheoremC
