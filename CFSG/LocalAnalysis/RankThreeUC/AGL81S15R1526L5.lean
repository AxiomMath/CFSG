module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526W
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.LThreeTwoPowCore
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O89Ctx2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526L2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526L3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526L4
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526LN
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0b
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526H
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526K
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KHupGeFive
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section FinalMain

variable {G : Type} [Group G] [Finite G]

private theorem two_le_pRank_three_of_row1520 {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hKSML3 : KSML3) (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (h3 : IsLThreeOfExp 1 ↥Ls) {I : Subgroup ↥M} (hI : I ≤ cMHat L)
    (hI3 : 1 ≤ CFSG.Open.pRank 3 I) :
    2 ≤ CFSG.Open.pRank 3 M := by
  obtain ⟨hbar, hZ⟩ := barO2_isLThree_of_lift hKSML3 ctx.gn hLs.1 hL h3
  have hq : Nat.Prime 3 := Nat.prime_three
  have hq2 : (3 : ℕ) ≠ 2 := by norm_num
  have hL1 : CFSG.Open.pRank 3 (barO2 L) = 1 :=
    (pRank_barO2_eq hL.1 hq hq2).symm.trans (pRank_eq_one_of_isLThree hL.1 hbar).1
  have hIge : 1 ≤ CFSG.Open.pRank 3 (barO2 I) := by
    rw [← pRank_barO2_eq_aux_eq I hq hq2]
    exact hI3
  have hc : ∀ a ∈ barO2 I, ∀ b ∈ barO2 L, a * b = b * a := by
    rintro _ ⟨i, hi, rfl⟩ b hb
    exact (Subgroup.mem_centralizer_iff.1 (hI hi) b hb).symm
  have hinf : barO2 I ⊓ barO2 L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.2⟩ : ↥(barO2 L)) ∈ Subgroup.center ↥(barO2 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc x hx.1 g g.2).symm
    rw [Subgroup.eq_bot_of_card_eq _ hZ, Subgroup.mem_bot] at hz
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)
  have hbot : CFSG.Open.pRank 3 (barO2 I ⊓ barO2 L) = 0 := by
    rw [hinf]
    exact pRank_eq_zero_of_not_dvd_s15 hq (by rw [Subgroup.card_bot]; norm_num)
  have hkey := pRank_add_le_pRank_sup_add_pRank_inf hc hq
  rw [hbot, add_zero] at hkey
  have hsup : CFSG.Open.pRank 3 (barO2 I ⊔ barO2 L) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    CFSG.SectionRank.pRank_mono hq.one_lt le_top
  have h2bar : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    omega
  have hEq := CFSG.SectionRank.pRank_quotient_two_group (CFSG.pCore 2 ↥M)
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) hq hq2
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← hEq]
  exact h2bar

theorem rowFinal_gen (hKSML3 : KSML3) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO89 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O89At G M)
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hLifts : RowLifts G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    (h25 : Row1525 G M T T₁ T₂) (h26 : Row1526W G M T T₁ T₂) (h27 : Row1527 G M T T₁ T₂)
    (h28 : Row1528 G M T T₁ T₂) :
    RowFinal G M T T₁ T₂ := by
  have hLN := hLN_of_rows_gen ctx.gn ctx.pair ctx.rank_N₁ ctx.rank_N₂ h25 h27
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  obtain ⟨Ls, hLs, -⟩ := exists_yComponent_dvd_ctx_gen kWiel_holds
    (kHupAt_odd (by norm_num) (by norm_num)) ctx h7
  obtain ⟨L, hL⟩ := hLifts Ls hLs
  have h3 : IsLThreeOfExp 1 ↥Ls := h25.2 Ls L hLs hL
  have hS : IsSimpleGroup ↥(Ystar (T.subgroupOf M) T₁ T₂) := isSimpleGroup_of_isLThreeOfExp_one h27
  have hmax : ∀ I ∈ CY (T.subgroupOf M) T₁ T₂,
      Nat.card ↥⁅I, gnV (T.subgroupOf M)⁆ ≤ Nat.card ↥⁅L, gnV (T.subgroupOf M)⁆ := by
    intro I hI
    rw [eq_of_mem_CY_of_simple ctx.gn hS hLs hL hI]
  have hW4 := (h26 Ls L hLs hL _ rfl).2.2.2 hmax
  have hY : yLifts (T.subgroupOf M) T₁ T₂ = L := yLifts_eq_of_simple ctx.gn hS hLs hL
  obtain ⟨hU0, hUT⟩ := uOf_props ctx.gn (T₁ := T₁) (T₂ := T₂) ⟨Ls, hLs, hL⟩
  obtain ⟨hW2, hW0⟩ := wSub_props M T ctx.sylow.isPGroup ⁅L, gnV (T.subgroupOf M)⁆
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact hUT hy) hU0
  have hTH := T_le_normalizer_wSub M T ⁅L, gnV (T.subgroupOf M)⁆
  have hNH := normalizer_le_normalizer_wSub M T ⁅L, gnV (T.subgroupOf M)⁆
  have hLH : L.map M.subtype ≤ Subgroup.normalizer
      ((wSub G M T ⁅L, gnV (T.subgroupOf M)⁆ : Subgroup G) : Set G) := by
    have := yLifts_le_normalizer_wSub_gen hKSML3 ctx.gn ctx.pair
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.good ctx) h25 hW4
    rwa [hY] at this
  obtain ⟨I, hI, hIc, hI1, hI3⟩ := (h20 7 h7 Ls L hLs hL).1
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 I
  obtain ⟨A, hA⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  obtain ⟨hbar, hZ⟩ := barO2_isLThree_of_lift hKSML3 ctx.gn hLs.1 hL h3
  have hA3 : Nat.card A = 3 := card_sylow_three_of_isLThree hL.1 hbar hA
  have hAU := (h28 7 h7 Ls L hLs hL I hI hIc hI1 hI3 Q A hQ (hY ▸ hA)).2.2
  have hM3 : 2 ≤ CFSG.Open.pRank 3 M :=
    two_le_pRank_three_of_row1520 hKSML3 ctx hLs hL h3 hI hI3
  have h3notM : (3 : ℕ) ∉ sigmaM G M := by
    rw [h25.1]
    simp
  have h3notA : (3 : ℕ) ∉ CFSG.Open.rankThreeSigmaA G := by
    intro h3A
    exact h3notM ⟨h3A, hM3⟩
  have hH3 : CFSG.Open.pRank 3
      (Subgroup.normalizer ((wSub G M T ⁅L, gnV (T.subgroupOf M)⁆ : Subgroup G) : Set G)) ≤ 3 :=
    ctx.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num) h3notA
      ⟨_, hW0, hW2, rfl⟩
  have hLn := hLN Ls L hLs hL
  have hLM : L.map M.subtype ≤ M := Subgroup.map_subtype_le L
  have h2 : IsPGroup 2 (CFSG.pPrimeCore 3 ↥(L.map M.subtype)) := by
    have h2L : IsPGroup 2 (CFSG.pPrimeCore 3 ↥L) := by
      rw [isPComponent_of_isLThree_aux4 hbar (Or.inl rfl : (3 : ℕ) = 3 ∨ (3 : ℕ) = 7)]
      exact isPComponent_of_isLThree_aux3 L
    let e : ↥L ≃* ↥(L.map M.subtype) := L.equivMapOfInjective M.subtype M.subtype_injective
    rw [← CFSG.pPrimeCore_map_iso 3 e]
    exact h2L.map e.toMonoidHom
  obtain ⟨S, hS2, hSM, hSN⟩ := hO89 _ ⟨_, hW0, hW2, rfl⟩ hH3
    (L.map M.subtype) (le_inf hLH hLM)
    (isPComponent_inf_of_isLThree hL.1 hbar (le_inf hLH hLM) inf_le_right)
    (by rw [pRank_map_subtype]; exact (pRank_eq_one_of_isLThree hL.1 hbar).1)
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.isLThreeTwoPow_pCore_of_pPrimeCore h2
      (isLThreeTwoPow_quotient_pPrimeCore hL.1 hbar))
    (A.map M.subtype) (Subgroup.map_mono hA.le)
    (by rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hA3) hAU
    (weak_closure_of_normal ctx.maxLocal hLn hA hA3 hAU)
  have hN := normalizer_inf_le_of_sylow ctx.sylow hTH hS2 hSM hSN
  intro g hg
  exact hN (Subgroup.mem_inf.mpr ⟨hg, hNH hg⟩)

theorem rowFinal (hKSML3 : KSML3) (hO89 : O89) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    (h25 : Row1525 G M T T₁ T₂) (h26 : Row1526W G M T T₁ T₂) (h27 : Row1527 G M T T₁ T₂)
    (h28 : Row1528 G M T T₁ T₂) :
    RowFinal G M T T₁ T₂ :=
  rowFinal_gen hKSML3 (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O89At.of_ctx2 hO89 ctx)
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.of_ctx2 ctx) hLifts h20 h25 h26 h27 h28

end FinalMain

section Skeleton

variable {G : Type} [Group G] [Finite G]

theorem s15_false (hK55 : K55) (hKSML3 : KSML3) (hKOut : KOut) (hO812 : O812six) (hP812 : P812)
    (hO991 : O991) (hO1218 : O1218) (hO98 : O98) (hO89 : O89) {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂) :
    False := by
  have h26 : Row1526W G M T T₁ T₂ := row1526 hK55 hKSML3 hKOut ctx h20 h25
  have h27 : Row1527 G M T T₁ T₂ := row1527 hKSML3 ctx hLifts h25 h26
  have h28 : Row1528 G M T T₁ T₂ :=
    row1528 hK55 hKSML3 hKOut hO812 hP812 hO991 hO1218 hO98 ctx hLifts h20 h25 h27
  exact ctx.notLe (rowFinal hKSML3 hO89 ctx hLifts h20 h25 h26 h27 h28)

end Skeleton

section SkeletonAll

theorem s15_skeleton (hK55 : K55) (hKSML3 : KSML3) (hKOut : KOut) (hO812 : O812six) (hP812 : P812)
    (hO991 : O991) (hO1218 : O1218) (hO98 : O98) (hO89 : O89)
    (hRows : ∀ (G : Type) [Group G] [Finite G], Standing G → ∀ (M T : Subgroup G)
      (T₁ T₂ : Subgroup ↥M), S15Ctx2 G M T T₁ T₂ →
        RowLifts G M T T₁ T₂ ∧ Row1520 G M T T₁ T₂ ∧ Row1525 G M T T₁ T₂) :
    ∀ (G : Type) [Group G] [Finite G], Standing G → ∀ (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M),
      S15Ctx2 G M T T₁ T₂ → False := by
  intro G _ _ hS M T T₁ T₂ ctx
  obtain ⟨hLifts, h20, h25⟩ := hRows G hS M T T₁ T₂ ctx
  exact s15_false hK55 hKSML3 hKOut hO812 hP812 hO991 hO1218 hO98 hO89 ctx hLifts h20 h25

end SkeletonAll

end CFSG.LocalAnalysis.RankThreeUC.S15
