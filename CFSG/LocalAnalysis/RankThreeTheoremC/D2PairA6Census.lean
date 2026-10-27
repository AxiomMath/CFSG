module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Ctx
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVTypes
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Residues
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.RankThreeCoreUniqueness.Helpers

theorem a6c_four_le_pRank_alt {N : ℕ} (hN : 12 ≤ N) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin N))) := by
  let j : Fin 4 × ZMod 3 → Fin N := fun p => ⟨3 * (p.1 : ℕ) + (p.2 : ZMod 3).val, by
    have h1 : (p.2 : ZMod 3).val < 3 := ZMod.val_lt _
    have h2 : (p.1 : ℕ) < 4 := p.1.2
    omega⟩
  have hj : Function.Injective j := by
    rintro ⟨i, t⟩ ⟨i', t'⟩ h
    have h1 : t.val < 3 := ZMod.val_lt _
    have h2 : t'.val < 3 := ZMod.val_lt _
    have h3 : 3 * (i : ℕ) + t.val = 3 * (i' : ℕ) + t'.val := congrArg Fin.val h
    have hi : (i : ℕ) = (i' : ℕ) := by omega
    have ht : t.val = t'.val := by omega
    exact Prod.ext (Fin.ext hi) (ZMod.val_injective 3 ht)
  obtain ⟨E, hE, hcard, -⟩ := exists_elemAbelian_fixing (fun _ => 0) j hj (fun _ _ => rfl)
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE (by simpa using hcard)

theorem a6c_false_of_nineThreeThree {G : Type} [Group G] [Finite G]
    (hT : CitedBlockTransvectionPLType) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h3 : NineThreeThree M S L)
    (hsolv : BlockPLThreeSolv M S L) (hr : 3 ≤ Open.pRank 3 L) : False := by
  have h3p : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hOrth, hU4, -⟩ := hT G M S L hK hA hL hX hS h3
  have hrb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq h3p (by norm_num) M L hL.le]
  have hperf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      Nat.Coprime 3 (Nat.card V) := fun V hV hVp =>
    (Nat.Prime.coprime_iff_not_dvd h3p).mpr (hsolv V hV hVp)
  have hm4 : ∀ (d : TauCeti.ValidLieTypeIndex) (m : ℕ) (q : TauCeti.PrimePower),
      (d.1 = .D m q ∨ d.1 = .twistedD m q) → 4 ≤ m := by
    intro d m q hd
    have h := d.2
    rcases hd with hd | hd <;> rw [hd] at h <;>
      exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd with hd | hd | ⟨rfl, hd⟩
    · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨φ⟩⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
      exact false_of_quotient_sp_of_three (k := m - 1)
        (by have := hm4 d m q (Or.inl hd); omega) ⟨q', hq', hd'⟩ hperf φ
    · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨φ⟩⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
      exact false_of_quotient_sp_of_three (k := m - 1)
        (by have := hm4 d m q (Or.inr hd); omega) ⟨q', hq', hd'⟩ hperf φ
    · obtain ⟨e6⟩ := hU4 d ⟨q, hq, hd⟩ ⟨e⟩
      obtain ⟨Y, hYP, hY, h3Y⟩ := exists_perfect_three_dvd_of_surjective_perm
        (by norm_num : 5 ≤ 6) e6.toMonoidHom e6.surjective
      exact hsolv Y hYP hY h3Y
  · have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3p.one_lt e).symm.trans hrb
    rcases hn with rfl | rfl | rfl
    · have hle := pRank_three_alternating_le (N := 5)
      omega
    · have hle := pRank_three_alternating_le (N := 6)
      omega
    · have hle := pRank_three_alternating_le (N := 8)
      omega

theorem pairBlockType3_of_cited {G : Type} [Group G] [Finite G] (h93 : Asc81bNineThree)
    (h85 : Asc81bEightFive) (hX : D1NoXBlock3 G)
    (hT : CFSG.AGLEmbedding.CitedBlockTransvectionPLType) : PairBlockType3 G := by
  intro P M A H R hctx L hL h3 hZ
  have h3p : Nat.Prime 3 := Nat.prime_three
  have hNX : NoXBlockFor G := noXBlockFor_of_setting hX hctx.setting
  have hpr := hctx.pair
  have hnot := hpr.nineThree_not_one h85 hNX hL
  have hsolv := blockPLThreeSolv_of_perfectThreePrime hpr hctx.perf hL
  have hM3 : Open.pRank 3 M ≤ 3 := by
    have h1 := local_pRank_le_evenRank 3 h3p (by norm_num) M hctx.esc.maxTwoLocal_M.1
    rw [hctx.setting.rank] at h1
    exact h1
  have hLM : Open.pRank 3 L ≤ Open.pRank 3 M :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3p hL.le
  have hrb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq h3p (by norm_num) M L hL.le]
  have hrq := pRank_top_quot_center_eq hL.le hZ
  rcases hpr.nineThree h93 hL with h1 | h2 | h3' | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hnot.1
  · exact h2
  · exact (a6c_false_of_nineThreeThree hT hpr.isKGroup.1 hpr.asc81bHyp hL hnot.1
      (hpr.not_isSylowTwoOf_inf h85 hNX hL) h3' hsolv h3).elim
  · exfalso
    rw [card_inf_centralizer_eq_card_center, h4.2.1] at hZ
    exact hZ (dvd_refl 3)
  · exfalso
    obtain ⟨-, ⟨e⟩, -⟩ := id h5
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3p.one_lt e).symm.trans hrb
    have hle := pRank_three_alternating_le (N := 7)
    omega
  · exfalso
    obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSix.le_four h6 hsolv
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3p.one_lt e).symm.trans hrq
    have hle := pRank_three_alternating_le (N := 2 * n)
    omega
  · exfalso
    obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSeven.le_four h7 hsolv
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3p.one_lt e).symm.trans hrb
    have hle := pRank_three_alternating_le (N := 4 * n)
    have h4' := a6c_four_le_pRank_alt (N := 4 * n) (by omega)
    omega
  · exact (not_nineThreeEight h8 hsolv).elim

end CFSG.LocalAnalysis.RankThreeTheoremC
