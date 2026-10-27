module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526W
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0b
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KHupGeFive
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Lift
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

section Row27Final

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_yLifts (hKSML3 : KSML3) {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T)
    (hL3 : ∀ (Ls : Subgroup (X ⧸ gnC T)) (L : Subgroup X), GNYComponent T T₁ T₂ Ls →
      LiftOf T L Ls → IsLThreeOfExp 1 ↥Ls)
    {I I' : Subgroup X} (hI : I ∈ CY T T₁ T₂) (hI' : I' ∈ CY T T₁ T₂) (hne : I ≠ I') :
    2 ≤ CFSG.Open.pRank 7 (yLifts T T₁ T₂) := by
  have hIc := hI
  have hIc' := hI'
  obtain ⟨Is, hIs, hIl⟩ := hI
  obtain ⟨Is', hIs', hIl'⟩ := hI'
  obtain ⟨hbar, hZ⟩ := barO2_isLThree_of_lift hKSML3 hX hIs.1 hIl (hL3 Is I hIs hIl)
  obtain ⟨hbar', -⟩ := barO2_isLThree_of_lift hKSML3 hX hIs'.1 hIl' (hL3 Is' I' hIs' hIl')
  have hs : CFSG.Open.pRank 7 ((Subgroup.center ↥(barO2 I)).map (barO2 I).subtype) ≤ 0 := by
    have : Subgroup.center ↥(barO2 I) = ⊥ := Subgroup.card_eq_one.1 hZ
    rw [this, Subgroup.map_bot,
      CFSG.LocalAnalysis.RankThreeTheoremC.pRank_bot_eq_zero (by norm_num)]
  have h := pRank_add_le_pRank_sup hIl.1 hIl'.1 hne (by norm_num) (by norm_num) hs
  have h1 := (pRank_eq_one_of_isLThree hIl.1 hbar).2
  have h2 := (pRank_eq_one_of_isLThree hIl'.1 hbar').2
  have hle : I ⊔ I' ≤ yLifts T T₁ T₂ :=
    sup_le (le_iSup₂ (f := fun L (_ : L ∈ CY T T₁ T₂) => L) I hIc)
      (le_iSup₂ (f := fun L (_ : L ∈ CY T T₁ T₂) => L) I' hIc')
  have := CFSG.SectionRank.pRank_mono (p := 7) (by norm_num) hle
  omega

theorem row1527_gen (hKSML3 : KSML3) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hLifts : RowLifts G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    (h26 : Row1526W G M T T₁ T₂) : Row1527 G M T T₁ T₂ := by
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  have hL3 : ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
        IsLThreeOfExp 1 ↥Ls := h25.2
  obtain ⟨Ls₀, hLs₀, -⟩ := exists_yComponent_dvd_ctx_gen kWiel_holds
    (kHupAt_odd (by norm_num) (by norm_num)) ctx h7
  obtain ⟨L₀, hL₀⟩ := hLifts Ls₀ hLs₀
  have hne : (CY (T.subgroupOf M) T₁ T₂).Nonempty := ⟨L₀, Ls₀, hLs₀, hL₀⟩
  obtain ⟨L, hLmem, hmax⟩ := Set.exists_max_image (CY (T.subgroupOf M) T₁ T₂)
    (fun I => Nat.card ↥⁅I, gnV (T.subgroupOf M)⁆) (Set.toFinite _) hne
  obtain ⟨Ls, hLs, hL⟩ := hLmem
  have hW4 := (h26 Ls L hLs hL _ rfl).2.2.2 hmax
  have huniq : ∀ I ∈ CY (T.subgroupOf M) T₁ T₂, ∀ I' ∈ CY (T.subgroupOf M) T₁ T₂, I = I' := by
    intro I hI I' hI'
    by_contra hne'
    obtain ⟨hU0, hUT⟩ := uOf_props ctx.gn (T₁ := T₁) (T₂ := T₂) ⟨Ls, hLs, hL⟩
    obtain ⟨hW2, hW0⟩ := wSub_props M T ctx.sylow.isPGroup ⁅L, gnV (T.subgroupOf M)⁆
      (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
        exact hUT hy) hU0
    obtain ⟨P, -, hw⟩ := ctx.witness 7 h7
    have hY := yLifts_le_normalizer_wSub_gen hKSML3 ctx.gn ctx.pair
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.good ctx) h25 hW4
    have hR := two_le_pRank_yLifts hKSML3 ctx.gn hL3 hI hI' hne'
    have hN := normalizer_le_of_two_le_pRank_gen hw hW0 hW2 (Subgroup.map_subtype_le _) hY
      (by rw [pRank_map_subtype]; exact hR)
    exact ctx.notLe ((normalizer_le_normalizer_wSub M T _).trans hN)
  show IsLThreeOfExp 1 ↥(Ystar (T.subgroupOf M) T₁ T₂)
  rw [ystar_eq_of_unique hLifts huniq hLs]
  exact hL3 Ls L hLs hL

theorem row1527 (hKSML3 : KSML3) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    (h26 : Row1526W G M T T₁ T₂) : Row1527 G M T T₁ T₂ :=
  row1527_gen hKSML3
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.of_ctx2 ctx) hLifts h25 h26

end Row27Final

end CFSG.LocalAnalysis.RankThreeUC.S15
