module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526W
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526C2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526L1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15TILemma
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

section Row26FourB

variable {G : Type} [Group G] [Finite G]

theorem row1526_four_commute_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (hK55 : K55)
    (hKSML3 : KSML3) (hKOut : KOut)
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    {L : Subgroup ↥M} (hL : L ∈ CY (T.subgroupOf M) T₁ T₂)
    (hmax : ∀ I ∈ CY (T.subgroupOf M) T₁ T₂,
      Nat.card ↥⁅I, gnV (T.subgroupOf M)⁆ ≤ Nat.card ↥⁅L, gnV (T.subgroupOf M)⁆)
    {g : G} (hgT : conjSub g (uOf M T L) ≤ T) {I : Subgroup ↥M}
    (hI : I ∈ CY (T.subgroupOf M) T₁ T₂) :
    ∀ a ∈ conjSub g (uOf M T L), ∀ b ∈ uOf M T I, a * b = b * a := by
  by_cases hg : g ∈ M
  · have hVea := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV
      (T.subgroupOf M) ctx.gn
    haveI : (gnV (T.subgroupOf M)).Normal := Subgroup.normalClosure_normal
    obtain ⟨Ls, hLs, hLL⟩ := hL
    obtain ⟨Is, hIs, hII⟩ := hI
    have hUL : (⁅L, gnV (T.subgroupOf M)⁆ : Subgroup ↥M) ≤ gnV (T.subgroupOf M) := by
      rw [Subgroup.commutator_comm]; exact commutator_gnV_le _ L
    have hUI : (⁅I, gnV (T.subgroupOf M)⁆ : Subgroup ↥M) ≤ gnV (T.subgroupOf M) := by
      rw [Subgroup.commutator_comm]; exact commutator_gnV_le _ I
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha₀
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    have h1 : (⟨g, hg⟩ : ↥M) * a' * (⟨g, hg⟩ : ↥M)⁻¹ ∈ gnV (T.subgroupOf M) :=
      (inferInstance : (gnV (T.subgroupOf M)).Normal).conj_mem a' (hUL ha') _
    have h2 := tiPair_comm hVea h1 (hUI hb')
    have h3 := congrArg Subtype.val h2
    simpa [MulAut.conj_apply] using h3
  · have hpair := row1526_four_pair_gen hK55 hKSML3 ctx h20 h25 hL hmax hgT hI
    exact row1526_four_contra_gen hK55 hKSML3 hKOut ctx h20 h25 hL hg hgT hI hpair

end Row26FourB

section Row26Four2

variable {G : Type} [Group G] [Finite G]

theorem row1526_four_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (hK55 : K55) (hKSML3 : KSML3)
    (hKOut : KOut)
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    {L : Subgroup ↥M} (hL : L ∈ CY (T.subgroupOf M) T₁ T₂)
    (hmax : ∀ I ∈ CY (T.subgroupOf M) T₁ T₂,
      Nat.card ↥⁅I, gnV (T.subgroupOf M)⁆ ≤ Nat.card ↥⁅L, gnV (T.subgroupOf M)⁆) :
    wSub G M T ⁅L, gnV (T.subgroupOf M)⁆ ≤ (Subgroup.centralizer
      ((⁅gnV (T.subgroupOf M), yLifts (T.subgroupOf M) T₁ T₂⁆ : Subgroup ↥M) : Set ↥M)).map
        M.subtype := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨⟨g, rfl⟩, hAT⟩ := hA
  have hTM : T ≤ M := ctx.sylow.le
  have hY := commutator_yLifts_le (T := T.subgroupOf M) (T₁ := T₁) (T₂ := T₂) ctx.gn
  intro a ha
  have haM : a ∈ M := hTM (hAT ha)
  refine Subgroup.mem_map.2 ⟨⟨a, haM⟩, ?_, rfl⟩
  have hS : (⨆ I ∈ CY (T.subgroupOf M) T₁ T₂, ⁅I, gnV (T.subgroupOf M)⁆) ≤
      Subgroup.centralizer (({⟨a, haM⟩} : Set ↥M)) := by
    refine iSup₂_le fun I hI b' hb' => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have := row1526_four_commute_gen hK55 hKSML3 hKOut ctx h20 h25 hL hmax hAT hI a ha (b' : G)
      (Subgroup.mem_map.2 ⟨b', hb', rfl⟩)
    exact Subtype.ext this
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := (Subgroup.mem_centralizer_iff.1 (hS (hY hh))) ⟨a, haM⟩ rfl
  exact this.symm

end Row26Four2

section Row26Main

variable {G : Type} [Group G] [Finite G]

theorem row1526_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (hK55 : K55) (hKSML3 : KSML3)
    (hKOut : KOut)
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂) :
    Row1526W G M T T₁ T₂ := by
  intro Ls L hLs hL U hU
  subst hU
  have hN := isNatSum_of_K55 hK55 ctx.gn hLs.1 (ctx.shape Ls hLs).1 (h25.2 Ls L hLs hL) hL
  refine ⟨hN, pElement_cMLStar_le_centralizer ctx.gn hLs.1 hL hN,
    row1526_three_gen hK55 ctx h20 h25 hLs hL, ?_⟩
  intro hmax
  exact row1526_four_gen hK55 hKSML3 hKOut ctx h20 h25 ⟨Ls, hLs, hL⟩ hmax

theorem row1526 {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (hK55 : K55) (hKSML3 : KSML3)
    (hKOut : KOut) (ctx : S15Ctx2 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    (h25 : Row1525 G M T T₁ T₂) :
    Row1526W G M T T₁ T₂ :=
  row1526_gen hK55 hKSML3 hKOut
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.of_ctx2 ctx) h20 h25

end Row26Main

end CFSG.LocalAnalysis.RankThreeUC.S15
