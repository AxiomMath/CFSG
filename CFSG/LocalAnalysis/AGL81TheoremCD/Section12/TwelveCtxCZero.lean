module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenOneCZeroProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreePerfectProof
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeASix
import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreeSolv

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.LocalAnalysis.RankThreeTheoremC.TenOneCZero
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

private theorem hasWGen_of_nineThreeTwo {M H L : Subgroup G} (hT : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive) (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hKL : KFactParabolicLeviMember) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (h2 : NineThreeTwo M (pCoreOf 2 H) L) :
    HasWGen (↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) := by
  have hns := (hT.nineThree_not_one hK h85 hD2 hL).2 h2
  obtain ⟨hcl, hpar, hO⟩ := h2
  rw [hO] at hns
  exact hKL _ _ _ hL.component.2.2
    (TenThreeThree.pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent) hcl hpar hns

private theorem hasWGen_of_nineThreeThree {M H L : Subgroup G}
    (hT : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive)
    (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hA : Asc81bHyp M (pCoreOf 2 H)) (hPL : CitedBlockTransvectionPLType)
    (h3 : NineThreeThree M (pCoreOf 2 H) L)
    (hQ : CFSG.pCore 2 (↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) = ⊥) :
    HasWGen (↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) := by
  have hX := (hT.nineThree_not_one hK h85 hD2 hL).1
  have hSy := hT.not_isSylowTwoOf_inf hK h85 hD2 hL
  rcases citedBlockTransvectionPL_of_type hPL G M (pCoreOf 2 H) L hK hA hL hX hSy h3 with
    ⟨k, d, hk, ⟨q, hq, hdq⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact (hasWGen_lie_typeB_two hq hk hdq).of_mulEquiv e
  · exact hasWGen_of_mulEquiv_perm e hQ (by omega)

private theorem hasWGen_of_nineThreeFour {M H L : Subgroup G}
    (h4 : NineThreeFour M (pCoreOf 2 H) L)
    (hPNL : barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≤ barM M L) :
    HasWGen (↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) := by
  obtain ⟨-, hZ, hA6, -, hS4⟩ := h4
  have hodd := (TenThreeThree.threeASix_odd hPNL hZ hA6 hS4).2
  by_contra hW
  rw [wSup_eq_bot_of_not_hasWGen hW, Subgroup.index_bot] at hodd
  exact hodd (two_dvd_card_hat_of_threeASix hPNL hZ hS4)

private theorem hasWGen_of_nineThreeSix {M H L : Subgroup G}
    (h6 : NineThreeSix M (pCoreOf 2 H) L)
    (hQ : CFSG.pCore 2 (↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) = ⊥)
    (hLq : Open.IsQuasisimple ↥(barM M L)) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    HasWGen (↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) := by
  obtain ⟨-, n, ⟨eL⟩, ⟨e⟩⟩ := h6
  refine hasWGen_of_mulEquiv_perm e hQ ?_
  by_contra hn
  haveI : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hLq.2.toNontrivial
  exact not_nontrivial_alternatingGroup_of_le_two (m := 2 * n) (by omega) eL.injective.nontrivial

private theorem hasWGen_of_nineThreeSeven {M H L : Subgroup G}
    (h7 : NineThreeSeven M (pCoreOf 2 H) L)
    (hQ : CFSG.pCore 2 (↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) = ⊥)
    (hLq : Open.IsQuasisimple ↥(barM M L)) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    HasWGen (↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) := by
  obtain ⟨-, n, ⟨eL⟩, ⟨e⟩⟩ := h7
  refine hasWGen_of_mulEquiv_perm e hQ ?_
  by_contra hn
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · haveI : Nontrivial ↥(barM M L) := by
      have := hLq.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
    exact not_nontrivial_alternatingGroup_of_le_two (m := 4 * 0) (by omega)
      eL.injective.nontrivial
  · haveI : Nontrivial ↥(barM M L) := by
      have := hLq.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
    haveI : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    haveI : Group.IsSolvable ↥(alternatingGroup (Fin (4 * 1))) :=
      subgroup_solvable_of_solvable _
    have hsol : Group.IsSolvable ↥(barM M L) :=
      solvable_of_solvable_injective (f := eL.toMonoidHom) eL.injective
    haveI : Group.IsPerfect ↥(barM M L) := ⟨hLq.1⟩
    exact Group.IsPerfect.not_isSolvable (↥(barM M L)) hsol

private theorem hasWGen_of_nineThreeEight {M H L : Subgroup G}
    (h8 : NineThreeEight M (pCoreOf 2 H) L) :
    HasWGen (↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) := by
  obtain ⟨-, N, r, hN, -, h0, h2, h4, -, φ, -, -⟩ := h8
  have hm : 5 ≤ N - 2 * r := by
    obtain ⟨j, hj⟩ := hN
    omega
  exact (hasWGen_perm_prod_of_five_le hm).of_mulEquiv φ

theorem cZero_inf_nonempty_of_twoLocalPhaseThree
    {M H L : Subgroup G}
    (hT : CFSG.AGLEmbedding.TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hKL : CFSG.LocalAnalysis.RankThreeTheoremC.TenOneCZero.KFactParabolicLeviMember)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hA7 : ¬ NineThreeFive M L) : (cZero (H ⊓ L)).Nonempty := by
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  have hLM : L ≤ M := hL.le
  have hXM : H ⊓ L ≤ M := inf_le_right.trans hLM
  suffices hW : HasWGen (↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L))) by
    rw [hNS] at hW
    exact cZero_nonempty_of_hasWGen hXM hW
  have hQ : CFSG.pCore 2 (↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L))) = ⊥ :=
    pCore_quotient_pCore_eq_bot' 2
  have hX : ¬ InClassXBlock L := (hT.nineThree_not_one hK h85 hD2 hL).1
  have hSy : ¬ IsSylowTwoOf (pCoreOf 2 H ⊓ L) L :=
    hT.not_isSylowTwoOf_inf hK h85 hD2 hL
  have hLq : Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have hPNL : barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L) ≤ barM M L :=
    Subgroup.map_mono fun y hy => by
      rw [mem_subgroupOf] at hy ⊢
      exact hy.2
  have hPL : CitedBlockTransvectionPLType :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
  rcases hT.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact hasWGen_of_nineThreeTwo hT hK h85 hD2 hKL hL h2
  · exact hasWGen_of_nineThreeThree hT hK h85 hD2 hL hA hPL h3 hQ
  · exact hasWGen_of_nineThreeFour h4 hPNL
  · exact (hA7 h5).elim
  · exact hasWGen_of_nineThreeSix h6 hQ hLq hL
  · exact hasWGen_of_nineThreeSeven h7 hQ hLq hL
  · exact hasWGen_of_nineThreeEight h8

theorem cZero_inf_nonempty_of_twelveCtx
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (h93 : Asc81bNineThree)
    (hKL : CFSG.LocalAnalysis.RankThreeTheoremC.TenOneCZero.KFactParabolicLeviMember)
    {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} (h : TwelveCtx G M p Q H) {L : Subgroup G}
    (hL : L ∈ weakBlockSet M H) (hA7 : ¬ NineThreeFive M L) :
    (cZero (H ⊓ L)).Nonempty := by
  haveI : IsSimpleGroup G := h.cstar.simple
  have hT : CFSG.AGLEmbedding.TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hK : Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper
      (twoLocal_ne_top h.cstar.nonab M h.maxLocal.1)
  have h85 : Asc81bEightFive :=
    CFSG.AGLEmbedding.asc81bEightFive_of_factorization
      (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs
        CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved)
  have hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
    noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  exact cZero_inf_nonempty_of_twoLocalPhaseThree hT hK h85 h93 hD2 hKL (by
    simpa [weakBlockSet] using hL) hA7

private theorem three_dvd_card_of_nineThreeTwo {M H L I : Subgroup G}
    {C' : Subgroup ↥(barM M (H ⊓ L))}
    (h2 : NineThreeTwo M (pCoreOf 2 H) L) (hPar : KFactParabolicPerfectThree)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L)
    (hC'card : Nat.card C' = Nat.card (barM M I))
    (hCP : barM M I ≤ barM M (H ⊓ L))
    (hCne : barM M I ≠ ⊥) (hCp : ⁅barM M I, barM M I⁆ = barM M I)
    (hCsn : ((barM M I).subgroupOf (barM M (H ⊓ L))).IsSubnormal) :
    3 ∣ Nat.card C' := by
  obtain ⟨hcl, hpar, -⟩ := h2
  rw [hNS] at hpar
  rw [hC'card]
  exact hPar _ _ _ hL.component.2.2
    (TenThreeThree.pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent) hcl hpar _ hCP hCne hCp hCsn

private theorem three_dvd_card_of_nineThreeThree {M H L : Subgroup G}
    {C' : Subgroup ↥(barM M (H ⊓ L))}
    (h3 : NineThreeThree M (pCoreOf 2 H) L) (hPL : CitedBlockTransvectionPLType)
    (hSp : KFactSpTwoPerfectThree) (hT : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive)
    (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hA : Asc81bHyp M (pCoreOf 2 H))
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L)
    (hPP : barM M (H ⊓ L) = blockPL M (pCoreOf 2 H) L)
    (hC'ne : C' ≠ ⊥) (hC'p : ⁅C', C'⁆ = C') (hCsn : C'.IsSubnormal) :
    3 ∣ Nat.card C' := by
  have hX := (hT.nineThree_not_one hK h85 hNX hL).1
  have hSy := hT.not_isSylowTwoOf_inf hK h85 hNX hL
  obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ := hPL G M (pCoreOf 2 H) L hK hA hL hX hSy h3
  have tr : ∀ {n : ℕ}, Nonempty (↥(blockPL M (pCoreOf 2 H) L) ≃* Equiv.Perm (Fin n)) →
      3 ∣ Nat.card C' := fun ⟨e⟩ =>
    CZeroThreePerfect.three_dvd_card_of_mulEquiv_perm
      ((MulEquiv.subgroupCongr hPP).trans e) hC'ne hC'p hCsn
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd'⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd' with hd' | hd' | ⟨rfl, hd'⟩
    · obtain ⟨d'', hd'', ⟨eP⟩⟩ := hOrth m d ⟨q, hq, Or.inl hd'⟩ ⟨e⟩
      obtain ⟨g1, g2, g3, g4⟩ := CZeroThreePerfect.quot_facts hC'ne hC'p hCsn
      have eQ : ↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)) ≃*
          (TauCeti.CFSGIndex.lie d'').Group :=
        (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hPP)
          (CFSG.pCore_map_iso 2 (MulEquiv.subgroupCongr hPP))).trans eP
      exact (hSp _ (m - 1) d'' hd'' ⟨eQ⟩ _ g1 g2 g3).trans g4
    · obtain ⟨d'', hd'', ⟨eP⟩⟩ := hOrth m d ⟨q, hq, Or.inr hd'⟩ ⟨e⟩
      obtain ⟨g1, g2, g3, g4⟩ := CZeroThreePerfect.quot_facts hC'ne hC'p hCsn
      have eQ : ↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)) ≃*
          (TauCeti.CFSGIndex.lie d'').Group :=
        (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hPP)
          (CFSG.pCore_map_iso 2 (MulEquiv.subgroupCongr hPP))).trans eP
      exact (hSp _ (m - 1) d'' hd'' ⟨eQ⟩ _ g1 g2 g3).trans g4
    · exact tr (hU4 d ⟨q, hq, hd'⟩ ⟨e⟩)
  · rcases hn with rfl | rfl | rfl
    · exact tr (hA5 ⟨e⟩)
    · exact tr (hA6 ⟨e⟩)
    · exact tr (hA8 ⟨e⟩)

private theorem three_dvd_card_of_nineThreeFour {M H L : Subgroup G}
    {C' : Subgroup ↥(barM M (H ⊓ L))}
    (h4 : NineThreeFour M (pCoreOf 2 H) L)
    (hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L)
    (hsolv : Group.IsSolvable (barM M (H ⊓ L)) → False) :
    3 ∣ Nat.card C' := by
  obtain ⟨-, -, -, -, ⟨eS4⟩⟩ := h4
  rw [hNS] at eS4
  have hs := CZeroThreePerfect.isSolvable_of_map_center_perm_four eS4
  have hPL' : barM M (H ⊓ L) ≤ barM M L := Subgroup.map_mono fun y hy => by
    rw [mem_subgroupOf] at hy ⊢
    exact hy.2
  set eP := (Subgroup.subgroupOfEquivOfLe hPL').symm
  exact (hsolv (solvable_of_solvable_injective (f := eP.toMonoidHom) eP.injective)).elim

private theorem three_dvd_card_of_nineThreeFive {M H L : Subgroup G}
    {C' : Subgroup ↥(barM M (H ⊓ L))}
    (h5' : NineThreeFive M L)
    (h5 : ∀ M S L : Subgroup G, Open.IsKGroup ↥M → Asc81bHyp M S → IsWeakSBlock M S L →
      ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L → NineThreeFive M L →
      Group.IsSolvable ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ∨
        Nat.card ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ∣ 72)
    (hT : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive)
    (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hA : Asc81bHyp M (pCoreOf 2 H))
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L)
    (hC'ne : C' ≠ ⊥) (hC'p : ⁅C', C'⁆ = C')
    (hsolv : Group.IsSolvable (barM M (H ⊓ L)) → False) :
    3 ∣ Nat.card C' := by
  have hX := (hT.nineThree_not_one hK h85 hNX hL).1
  have hSy := hT.not_isSylowTwoOf_inf hK h85 hNX hL
  rcases h5 M (pCoreOf 2 H) L hK hA hL hX hSy h5' with hs | hc
  · rw [hNS] at hs
    exact (hsolv hs).elim
  · rw [hNS] at hc
    have hC72 : Nat.card C' ∣ 72 := (Subgroup.card_subgroup_dvd_card C').trans hc
    by_contra h3
    have h8 : Nat.card C' ∣ 2 ^ 3 := by
      have hcop : Nat.Coprime (Nat.card C') 9 :=
        Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
      exact hcop.dvd_of_dvd_mul_right (by simpa using hC72)
    obtain ⟨k, -, hk8⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h8
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hC'ne (CZeroThreePerfect.eq_bot_of_perfect_of_isPGroup (IsPGroup.of_card hk8) hC'p)

private theorem three_dvd_card_of_nineThreeSix {M H L : Subgroup G}
    {C' : Subgroup ↥(barM M (H ⊓ L))}
    (h6 : NineThreeSix M (pCoreOf 2 H) L)
    (hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L)
    (hC'ne : C' ≠ ⊥) (hC'p : ⁅C', C'⁆ = C') (hCsn : C'.IsSubnormal) :
    3 ∣ Nat.card C' := by
  obtain ⟨-, n, -, hPn⟩ := h6
  replace hPn := CZeroThreePerfect.quotPCore_congr (congrArg (barM M) hNS) hPn
  exact CZeroThreePerfect.three_dvd_of_quot_perm hC'ne hC'p hCsn hPn

private theorem three_dvd_card_of_nineThreeSeven {M H L : Subgroup G}
    {C' : Subgroup ↥(barM M (H ⊓ L))}
    (h7 : NineThreeSeven M (pCoreOf 2 H) L)
    (hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L)
    (hC'ne : C' ≠ ⊥) (hC'p : ⁅C', C'⁆ = C') (hCsn : C'.IsSubnormal) :
    3 ∣ Nat.card C' := by
  obtain ⟨-, n, -, hPn⟩ := h7
  replace hPn := CZeroThreePerfect.quotPCore_congr (congrArg (barM M) hNS) hPn
  exact CZeroThreePerfect.three_dvd_of_quot_perm hC'ne hC'p hCsn hPn

private theorem three_dvd_card_of_nineThreeEight {M H L : Subgroup G}
    {C' : Subgroup ↥(barM M (H ⊓ L))}
    (h8 : NineThreeEight M (pCoreOf 2 H) L)
    (hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L)
    (hC'ne : C' ≠ ⊥) (hC'p : ⁅C', C'⁆ = C') (hCsn : C'.IsSubnormal) :
    3 ∣ Nat.card C' := by
  obtain ⟨-, N, r, -, -, -, -, -, -, φ, -, -⟩ := h8
  have hφ : Nonempty (↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ≃*
        Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))) := ⟨φ⟩
  replace hφ := CZeroThreePerfect.quotPCore_congr (congrArg (barM M) hNS) hφ
  exact CZeroThreePerfect.three_dvd_of_quot_perm_prod hC'ne hC'p hCsn hφ

private theorem three_dvd_card_of_image {M H L I : Subgroup G}
    {C' : Subgroup ↥(barM M (H ⊓ L))}
    (hT : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M)
    (h85 : Asc81bEightFive) (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hPL : CitedBlockTransvectionPLType) (hPar : KFactParabolicPerfectThree)
    (hSp : KFactSpTwoPerfectThree)
    (h5 : ∀ M S L : Subgroup G, Open.IsKGroup ↥M → Asc81bHyp M S → IsWeakSBlock M S L →
      ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L → NineThreeFive M L →
      Group.IsSolvable ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ∨
        Nat.card ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ∣ 72)
    (hA : Asc81bHyp M (pCoreOf 2 H)) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L)
    (hC'card : Nat.card C' = Nat.card (barM M I))
    (hC'ne : C' ≠ ⊥) (hC'p : ⁅C', C'⁆ = C') (hC'sn : C'.IsSubnormal)
    (hCP : barM M I ≤ barM M (H ⊓ L))
    (hCne : barM M I ≠ ⊥) (hCp : ⁅barM M I, barM M I⁆ = barM M I)
    (hCsn : ((barM M I).subgroupOf (barM M (H ⊓ L))).IsSubnormal)
    (hsolv : Group.IsSolvable (barM M (H ⊓ L)) → False)
    (h : NineThreeConclusion M (pCoreOf 2 H) L) :
    3 ∣ Nat.card C' := by
  rcases h with h1 | h2 | h3 | h4 | h5' | h6 | h7 | h8
  · exact absurd h1 (hT.nineThree_not_one hK h85 hNX hL).1
  · exact three_dvd_card_of_nineThreeTwo h2 hPar hL hNS hC'card hCP hCne hCp hCsn
  · exact three_dvd_card_of_nineThreeThree h3 hPL hSp hT hK h85 hNX hA hL hNS
      (by rw [← hNS]) hC'ne hC'p hC'sn
  · exact three_dvd_card_of_nineThreeFour h4 hNS hsolv
  · exact three_dvd_card_of_nineThreeFive h5' h5 hT hK h85 hNX hA hL hNS hC'ne hC'p hsolv
  · exact three_dvd_card_of_nineThreeSix h6 hNS hC'ne hC'p hC'sn
  · exact three_dvd_card_of_nineThreeSeven h7 hNS hC'ne hC'p hC'sn
  · exact three_dvd_card_of_nineThreeEight h8 hNS hC'ne hC'p hC'sn

theorem three_dvd_card_oUpperTwo_of_perfect_member {M H : Subgroup G}
    (hT : CFSG.AGLEmbedding.TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hPL : CitedBlockTransvectionPLType)
    (hPar : KFactParabolicPerfectThree) (hSp : KFactSpTwoPerfectThree)
    (h5 : ∀ M S L : Subgroup G, Open.IsKGroup ↥M → Asc81bHyp M S → IsWeakSBlock M S L →
      ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L → NineThreeFive M L →
      Group.IsSolvable ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ∨
        Nat.card ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ∣ 72)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {I : Subgroup G}
    (hI : I ∈ cZero (H ⊓ L)) (hIc : IsTwoPrimeComponent I I) :
    3 ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I) := by
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  have hLM : L ≤ M := hL.le
  refine CZeroThreePerfect.three_dvd_card_oUpperTwo ?_
  have hI1 : I ≠ ⊥ := by
    have h1 : Nontrivial ↥(barM I I) := by
      have := hIc.component.2.2.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM I I))).nontrivial
    have h2 : Nontrivial (↥I ⧸ CFSG.pCore 2 ↥I) :=
      Function.Injective.nontrivial (f := (barM I I).subtype) (barM I I).subtype_injective
    have h3 : Nontrivial ↥I := (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot I).mp h3
  obtain ⟨hCP, hCne, hCp, hCsn, hCdvd⟩ := CZeroThreePerfect.barM_facts hLM hI.le hI.subnormal
    hIc.perfect hI1
  refine Dvd.dvd.trans ?_ hCdvd
  set C' := (barM M I).subgroupOf (barM M (H ⊓ L)) with hC'
  have hC'card : Nat.card C' = Nat.card (barM M I) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv
  have hC'ne : C' ≠ ⊥ := by
    intro h
    apply hCne
    rw [← Subgroup.map_subgroupOf_eq_of_le hCP, ← hC', h, Subgroup.map_bot]
  have hC'p : ⁅C', C'⁆ = C' := by
    apply Subgroup.map_injective (barM M (H ⊓ L)).subtype_injective
    rw [Subgroup.map_commutator, hC', Subgroup.map_subgroupOf_eq_of_le hCP]
    exact hCp
  rw [← hC'card]
  have hsolv : Group.IsSolvable (barM M (H ⊓ L)) → False := fun hs => by
    have := CZeroThreePerfect.eq_bot_of_perfect_of_isSolvable hC'p
    exact hC'ne this
  exact three_dvd_card_of_image hT hK h85 hNX hPL hPar hSp h5 hA hL hNS hC'card hC'ne hC'p
    hCsn hCP hCne hCp hCsn hsolv (hT.nineThree hK h93 hL)

theorem three_dvd_card_oUpperTwo_of_twelveCtx
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (h93 : Asc81bNineThree)
    (hPar : KFactParabolicPerfectThree) (hSp : KFactSpTwoPerfectThree) {M : Subgroup G}
    {p : ℕ} {Q H : Subgroup G} (h : TwelveCtx G M p Q H) {L : Subgroup G}
    (hL : L ∈ weakBlockSet M H) {I : Subgroup G} (hI : I ∈ cZero (H ⊓ L)) :
    3 ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I) := by
  haveI : IsSimpleGroup G := h.cstar.simple
  have hT : CFSG.AGLEmbedding.TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hK : Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper
      (twoLocal_ne_top h.cstar.nonab M h.maxLocal.1)
  have h85 : Asc81bEightFive :=
    CFSG.AGLEmbedding.asc81bEightFive_of_factorization
      (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs
        CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved)
  have hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
    noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  have hL' : IsWeakSBlock M (pCoreOf 2 H) L := by simpa [weakBlockSet] using hL
  rcases hI.shape with hIc | ⟨-, hsym⟩
  · exact three_dvd_card_oUpperTwo_of_perfect_member hT hK h85 h93 hNX
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds hPar hSp
      (fun M S L hKM hA hLW hX hSy h5 =>
        Or.inr (CFSG.AGLEmbedding.citedBlockAltSevenPL_holds G M S L hKM hA hLW hX hSy h5))
      hL' hI hIc
  · exact three_dvd_card_oUpperTwo_of_symThree hsym

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
