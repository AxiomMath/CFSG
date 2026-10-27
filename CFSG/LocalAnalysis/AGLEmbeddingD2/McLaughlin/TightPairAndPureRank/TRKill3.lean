module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRKill2
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem false_of_card_alt {X : Type} [Group X] (h : Nat.card X = 9999360) {m : ℕ}
    (hm5 : 5 ≤ m) (hm : m ≤ 16) (e : X ≃* alternatingGroup (Fin m)) : False := by
  have h1 := (Nat.card_congr e.toEquiv).symm.trans h
  rw [card_alt_fin (by omega)] at h1
  interval_cases m <;> norm_num [Nat.factorial] at h1

section Shape

variable {G : Type} [Group G] [Finite G]

theorem engineBlock_of_shape (hK2 : KFactOrthogonalTwoLieRank) (hK3 : KFactNineThreeThreeBig)
    (hK5 : KFactNineThreeThreeFive) (h418 : Agl418) (hL5 : L5Atlas)
    {M S L : Subgroup G} (hKM : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hw : IsWeakSBlock M S L)
    (hnS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hconc : NineThreeConclusion M S L) (hnot1 : ¬ NineThreeOne L)
    (hsolv : BlockPLThreeSolv M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hshape : Open.pRank 3 L ≤ 1 ∨
      IsL5Two (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) :
    PairTwoEngineBlock M S L := by
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hw.component.2.2
  have hperf : ⁅L, L⁆ = L := hw.perfect
  have hrb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq Nat.prime_three
      (by norm_num) M L hw.le]
  have hrq := pRank_top_quot_center_eq hw.le hZ
  have hnt : Nontrivial ↥(barM M L) := by
    haveI := hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
  have hperfX : commutator ↥(barM M L) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (barM_perfect hw.le hperf))
  have hgen : ∀ m : ℕ, 5 ≤ m → m ≤ 16 →
      (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m)) →
      (m = 5 → Open.pRank 3 L ≤ 1 → False) → False := by
    intro m h5 h16 e h5hyp
    rcases hshape with hr | h5'
    · by_cases hm5 : m = 5
      · exact h5hyp hm5 hr
      · have h2 := le_pRank_alternatingGroup_three (N := m) (k := 2) (by omega)
        have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
          hrq
        omega
    · exact false_of_card_alt (hL5 _ h5').1 h5 h16 e
  rcases hconc with h1 | h2 | hT3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hnot1
  · exact engineBlock_of_nineThreeTwo h2
  · exfalso
    have hT3' := hT3
    obtain ⟨-, horth, -⟩ := hT3
    rcases horth with ⟨d, ⟨m, q, hq2, hD⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
      have hrk0 := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
        hrb
      have h2le := hK2 ↥(barM M L) d ⟨m, q, hq2, hD⟩ ⟨e⟩
      by_cases hr3 : 3 ≤ Open.pRank 3 L
      · exact hK3 G M S L hKM hA hw hnot1 hnS hT3' hr3 hsolv
      · have hr2 : Open.pRank 3 L = 2 := by omega
        have hp2 := PrimePower.p_eq_two_of_card_eq_two hq2
        have hd : IsClassicalOrG2Index d.1 := by
          rcases hD with h | h | ⟨-, h⟩ <;> rw [h] <;> simp [IsClassicalOrG2Index, hp2]
        have hrk : Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 2 := by omega
        have hlist := h418 d hd hrk
        have hmod : q.card % 3 = 2 := by rw [hq2]
        rcases hD with h | h | ⟨hm, h⟩ <;>
          rcases hlist with ⟨q', hq'⟩ | ⟨q', hq'⟩ | ⟨q', hq', h3⟩ | ⟨q', hq', h3⟩ | ⟨q', hq', h3⟩ |
            ⟨q', hq', h3⟩ | ⟨q', hq', h3⟩ | ⟨q', hq', h3⟩ <;>
          simp_all
    · have hn5 : 5 ≤ n := five_le_of_perfect_alt hperfX e
      obtain ⟨e'⟩ := quotCenterEquivAlt hn5 e
      refine hgen n hn5 (by omega) e' fun hm _ => ?_
      subst hm
      exact hnot1 (hK5 G M S L hw hT3' ⟨e⟩)
  · exfalso
    obtain ⟨-, hc3, -⟩ := h4
    apply hZ
    rw [card_inf_centralizer_eq_card_center, hc3]
  · exfalso
    obtain ⟨-, ⟨e⟩, -⟩ := h5
    obtain ⟨e'⟩ := quotCenterEquivAlt (by norm_num : 5 ≤ 7) e
    exact hgen 7 (by norm_num) (by norm_num) e' fun h => by omega
  · exfalso
    obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSix.le_four h6 hsolv
    have h5n : 5 ≤ 2 * n := five_le_of_quasisimple_cover_alt hw.le hperf hq e
    exact hgen (2 * n) h5n (by omega) e fun h => by omega
  · exfalso
    obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSeven.le_four h7 hsolv
    have h5n : 5 ≤ 4 * n := five_le_of_perfect_alt hperfX e
    obtain ⟨e'⟩ := quotCenterEquivAlt h5n e
    exact hgen (4 * n) h5n (by omega) e' fun h => by omega
  · exact (not_nineThreeEight h8 hsolv).elim

end Shape


theorem pairTwoBadShape2Residue_of_cited (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hPL : KFactBlockPLSylow) (hK2 : KFactOrthogonalTwoLieRank)
    (hK32 : KFactNineThreeThreeTwo) (hK5 : KFactNineThreeThreeFive) (h418 : Agl418)
    (hL5 : L5Atlas) : PairTwoBadShape2Residue := by
  have hK3 : KFactNineThreeThreeBig := kFactNineThreeThreeBig_of_two hK32
  have hA8 := pairNineThreeThreeA8Kill_of_two hK32
  intro G _ _ P M A H R hctx hev L₁ L₂ h₁ h₂ hne hk2 hZ₁ hZ₂ L hL hbad
  have hLF' := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hLF'
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  obtain ⟨hshape, hnot⟩ := hbad
  have hw : IsWeakSBlock M (pCoreOf 2 H) L := by
    rcases hL with rfl | hL
    · exact h₁
    · rw [Set.mem_singleton_iff.mp hL]; exact h₂
  have hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
    rcases hL with rfl | hL
    · exact hZ₁
    · rw [Set.mem_singleton_iff.mp hL]; exact hZ₂
  have hsolv := d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair
    hctx.strong hctx.perf L hw
  have hn1 := hctx.pair.nineThree_not_one h85 hX hw
  have hconc := hctx.pair.nineThree h93 hw
  rcases hshape with a | hA8' | l5
  · exact hnot (engineBlock_of_shape hK2 hK3 hK5 h418 hL5 hctx.pair.isKGroup.1 hctx.pair.asc81bHyp hw
      (hctx.pair.not_isSylowTwoOf_inf h85 hX hw) hconc hn1.1 hsolv hZ (Or.inl a))
  · have hthree := hctx.pair.blockHasThree h85 h86 h93 hX kFactParabolicThree
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hw
    exact hnot (engineBlock_of_A8 hw hconc hn1.1 hthree hsolv hZ hA8'
      (fun h => hA8 G M _ L hctx.pair.isKGroup.1 hctx.pair.asc81bHyp hw hn1.1
        (hctx.pair.not_isSylowTwoOf_inf h85 hX hw) h hZ hA8' hsolv)
      (fun h => hPL G P M A H R hctx L hw h hA8'))
  · exact hnot (engineBlock_of_shape hK2 hK3 hK5 h418 hL5 hctx.pair.isKGroup.1 hctx.pair.asc81bHyp hw
      (hctx.pair.not_isSylowTwoOf_inf h85 hX hw) hconc hn1.1 hsolv hZ (Or.inr l5))

end CFSG.AGLEmbeddingD2.McLaughlin
