module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Ctx
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieBuild
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Residues
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem card_le_nine_of_isPGroup_barM_inf (hpr : AGLPair 3 M H R) (hR9 : Nat.card R = 9)
    {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hT3 : IsPGroup 3 T) (hT : T ≤ barM M (H ⊓ M)) :
    Nat.card T ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQT : pCoreOf 2 M ≤ H ⊓ M :=
    le_inf (hpr.twoCore_M_le.trans (pCoreOf_le 2 H)) (pCoreOf_le 2 M)
  obtain ⟨B, hBT, hB3, hBc⟩ := exists_isPGroup_le_of_le_barM inf_le_right hQT (by norm_num) hT3 hT
  have hBH : B ≤ H := hBT.trans inf_le_left
  have hB' : IsPGroup 3 (B.subgroupOf H) := hB3.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨Q, hQ⟩ := hB'.exists_le_sylow
  obtain ⟨T0, hT0⟩ := hpr.isSylow
  have h1 : Nat.card (B.subgroupOf H) ≤ Nat.card (Q : Subgroup ↥H) := Subgroup.card_le_of_le hQ
  have h2 : Nat.card (Q : Subgroup ↥H) = Nat.card (T0 : Subgroup ↥H) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h3 : Nat.card ((T0 : Subgroup ↥H).map H.subtype) = Nat.card (T0 : Subgroup ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have h4 : Nat.card (B.subgroupOf H) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  rw [hT0, hR9] at h3
  omega

theorem false_of_oneImage_list3 (hLie : PairOneImageLieTR3 G) (hIrr : KFactBlockOneImageIrr3)
    (hctx : PairCtx3 P M A H R) (hev : 2 ∣ (H ⊓ M).relIndex H) (hRel : IsElemAbelian 3 R)
    (hR9 : Nat.card R = 9)
    (hirr : IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h2 : NineThreeTwo M (pCoreOf 2 H) L) (hr3 : 3 ≤ Open.pRank 3 L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : False := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hpr := hctx.pair
  have hlist := hLie P M A H R hctx hev L hL hk1 h2 hr3 hZ
  have hM3' : Open.pRank 3 M ≤ 3 := by
    have h1 := local_pRank_le_evenRank 3 h3 (by norm_num) M hctx.esc.maxTwoLocal_M.1
    rw [hctx.setting.rank] at h1
    exact h1
  have hSolv : BlockPLThreeSolv M (pCoreOf 2 H) L :=
    blockPLThreeSolv_of_perfectThreePrime hpr hctx.perf hL
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set PL := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPL
  have hRM : R ≤ M := hpr.le_M
  set Eb := barM M R with hEb
  have hEbel : IsElemAbelian 3 Eb := CFSG.AGLEmbeddingD2.isElemAbelian_barM hRel
  have hEb9 : Nat.card Eb = 9 := (card_barM_of_isPGroup_three hpr.isPGroup_R hRM).trans hR9
  have hnS : ∀ n ∈ H ⊓ M, n ∈ Subgroup.normalizer (S : Set G) := fun n hn => by
    rw [hpr.normalizer_twoCore_H]
    exact hn.1
  have hN : ∀ n ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), ∀ hn : n ∈ M,
      mk ⟨n, hn⟩ ∈ Subgroup.normalizer (Eb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (PL : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro n hn hnM
    have hb := mk_mem_normalizer_blocks hL hk1 hnM (hnS n hn.1)
    refine ⟨⟨?_, hb.2⟩, hb.1⟩
    have hRn : R.map (MulAut.conj n).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
    have := barM_map_conj hnM R
    rw [hRn] at this
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this.symm
  have hirrE := irreducibleOn_barM hirr hRM _ hN
  have hEPL : Eb ≤ PL := by
    obtain ⟨y, hyP, hy3, hyC⟩ := hy
    exact barM_le_PL_of_irreducible hpr hL hk1 hirr
      ⟨y, hyP, fun h => hyC (h ▸ Subgroup.one_mem _), hy3⟩
  have hord9 : ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      T ≤ PL → IsPGroup 3 T → Nat.card T ≤ 9 := by
    intro T' hT' hT3
    refine card_le_nine_of_isPGroup_barM_inf hpr hR9 hT3 (hT'.trans (barM_mono ?_))
    intro x hx
    have hxH : x ∈ H := by
      have := hx.1
      rwa [hpr.normalizer_twoCore_H] at this
    exact ⟨hxH, hL.le hx.2⟩
  exact hIrr G M S L hpr.isKGroup.1 hpr.asc81bHyp hL h2 hSolv hM3' hlist Eb hEbel hEb9 hEPL
    hord9 hirrE

end CFSG.LocalAnalysis.RankThreeTheoremC
