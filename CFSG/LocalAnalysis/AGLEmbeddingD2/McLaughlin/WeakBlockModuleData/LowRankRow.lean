module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TwoPureA6U33

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Open CFSG.QuasithinUnique

@[expose] def OutL27 : Prop :=
  ∀ (X : Type) [Group X], IsLThreeTwo X → AutThreePowInner X

@[expose] def KFactLowRankNineThreeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L) → BlockPLThreeSolv M S L →
    Open.pRank 3 L ≤ 1 →
    ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    IsLThreeTwo (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))

@[expose] def KFactOrthogonalTwoLieRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (d : TauCeti.ValidLieTypeIndex),
    (∃ m : ℕ, ∃ q : TauCeti.PrimePower, q.card = 2 ∧
      (d.1 = .D m q ∨ d.1 = .twistedD m q ∨ (m = 3 ∧ d.1 = .twistedA 3 q))) →
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
    2 ≤ Open.pRank 3 (⊤ : Subgroup Y)

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_mulEquiv_alt {X : Type*} [Group X] {N : ℕ} (hN : 4 ≤ N)
    (e : X ≃* alternatingGroup (Fin N)) : Subgroup.center X = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hc : e z ∈ Subgroup.center (alternatingGroup (Fin N)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    have := hz (e.symm y)
    simpa using congrArg e this
  rw [alternatingGroup.center_eq_bot (by simpa using hN), Subgroup.mem_bot] at hc
  exact e.injective (by simpa using hc)

theorem clauseO_of_lowRank (hL27 : OutL27) (hK1 : KFactLowRankNineThreeTwo)
    (hK2 : KFactOrthogonalTwoLieRank) {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (hconc : NineThreeConclusion M S L) (hnot1 : ¬ NineThreeOne L)
    (hSyl : NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L))
    (hsolv : BlockPLThreeSolv M S L) (hr : Open.pRank 3 L ≤ 1)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    ClauseO M L := by
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have hperf : ⁅L, L⁆ = L := hL.perfect
  have hrb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq Nat.prime_three
      (by norm_num) M L hL.le]
  have hrq := pRank_top_quot_center_eq hL.le hZ
  have hnt : Nontrivial ↥(barM M L) := by
    haveI := hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
  have hperfX : commutator ↥(barM M L) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hperf))
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hnot1
  · exact clauseO_of_cover hL.le hperf (hL27 _ (hK1 G M S L hL h2 (hSyl h2) hsolv hr hZ))
      (MulEquiv.refl _)
  · obtain ⟨-, horth, -⟩ := h3
    rcases horth with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exfalso
      have h2 := hK2 ↥(barM M L) d hd ⟨e⟩
      omega
    · have hn5 : 5 ≤ n := five_le_of_perfect_alt hperfX e
      have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
        hrb
      rcases hn with rfl | rfl | rfl
      · have hc := center_eq_bot_of_mulEquiv_alt (by norm_num) e
        exact clauseO_of_cover hL.le hperf (autThreePowInner_alt_of_five_le (N := 5) le_rfl)
          (((QuotientGroup.quotientMulEquivOfEq hc).trans
            (QuotientGroup.quotientBot (G := ↥(barM M L)))).trans e)
      · exfalso
        have := two_le_pRank_alternatingGroup_six
        omega
      · exfalso
        have := le_pRank_alternatingGroup_three (N := 8) (k := 2) (by norm_num)
        omega
  · exfalso
    obtain ⟨-, hc3, -⟩ := h4
    apply hZ
    rw [card_inf_centralizer_eq_card_center, hc3]
  · exfalso
    obtain ⟨-, ⟨e⟩, -⟩ := h5
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans hrb
    have := le_pRank_alternatingGroup_three (N := 7) (k := 2) (by norm_num)
    omega
  · exfalso
    obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSix.le_four h6 hsolv
    have h5n : 5 ≤ 2 * n := five_le_of_quasisimple_cover_alt hL.le hperf hq e
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
      hrq
    have := le_pRank_alternatingGroup_three (N := 2 * n) (k := 2) (by omega)
    omega
  · exfalso
    obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSeven.le_four h7 hsolv
    have h5n : 5 ≤ 4 * n := five_le_of_perfect_alt hperfX e
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans hrb
    have := le_pRank_alternatingGroup_three (N := 4 * n) (k := 2) (by omega)
    omega
  · exact (not_nineThreeEight h8 hsolv).elim

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
