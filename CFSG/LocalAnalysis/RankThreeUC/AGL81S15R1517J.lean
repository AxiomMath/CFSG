module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KOutLin
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421Cut
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89Sp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesAt
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517F
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517G
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517G0
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517H
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517I
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511Y
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

theorem row1518 {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (h13 : Row1513 G M T T₁ T₂) (h17 : Row1517 G M T T₁ T₂) : Row1518 G M T T₁ T₂ := by
  intro p hp Ls L hLs hL
  by_contra hcon
  have h3 : 2 < CFSG.Open.pRank p L := by omega
  exact (h17 p hp Ls L hLs hL).2 (h13 p hp Ls L hLs hL h3)

theorem row1517_of_core {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (core : ∀ p ∈ sigmaM G M, ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
        Bad1517 p ↥Ls → False) : Row1517 G M T T₁ T₂ := by
  intro p hp Ls L hLs hL
  exact ⟨fun h h7 => core p hp Ls L hLs hL (Or.inl ⟨h, h7⟩),
    fun h => core p hp Ls L hLs hL (Or.inr h)⟩

section GLevel2

variable {G : Type} [Group G] [Finite G]

theorem false_of_strong_three_core_gen (hK518 : K518) (hK517 : K517_6) (hK89 : K89Sp)
    (hK3 : K3DvdL3) (hKSML3 : KSML3) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂)
    (hstrong3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M)
    (h₁ : CFSG.Open.pRank 3 (Subgroup.normalizer (T₁ : Set ↥M)) ≤ 1)
    (h₂ : CFSG.Open.pRank 3 (Subgroup.normalizer (T₂ : Set ↥M)) ≤ 1)
    (hX3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥M))
    {Ls₀ : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs₀ : GNYComponent (T.subgroupOf M) T₁ T₂ Ls₀) (hL : LiftOf (T.subgroupOf M) L Ls₀)
    (hnotU4 : ¬ IsUFourOdd ↥Ls₀) : False := by
  have huniq : ∀ Is, GNYComponent (T.subgroupOf M) T₁ T₂ Is → Is = Ls₀ := fun Is hIs =>
    gnYComponent_unique (S15CtxGen.good ctx).three h₁ hIs hLs₀
  obtain ⟨Ls, hLs, hnorm, hC, hle, hy, -, hcase⟩ :=
    xlevel_three_branch_gen hK518 hK517 ctx.gn (S15CtxGen.good ctx) h₁ h₂ hX3 hLs₀ hL
  have hLs0 : Ls = Ls₀ := huniq Ls hLs
  subst hLs0
  rcases hcase with hU | ⟨-, hL3⟩
  · exact hnotU4 hU
  · have key : ∀ Ti : Subgroup ↥M, Ti ≠ ⊥ → Ti ≤ T.subgroupOf M →
        (Ti.subgroupOf (T.subgroupOf M)).Characteristic →
        CFSG.Open.pRank 3 (normalizer (Ti : Set ↥M)) ≤ 1 →
        HasLThreeCore (gnA (T.subgroupOf M) Ti Ls) → False := by
      intro Ti hne hle' hchar hrk hL3'
      obtain ⟨Y, hY, hYq⟩ := exists_Y_O2form hKSML3 ctx.gn hLs.1 hL hC hL3'
      exact false_of_Y_O2form_gen hK89 hK3 ctx.cstar.toStandingGen ctx.sylow ctx.notLe hstrong3
        hne hle' hchar hrk hY hYq
    rcases hL3 with h | h
    · exact key T₁ ctx.pair.ne_bot₁ (ctx.pair.le_center.trans (omegaOneCenterOf_le_subgroup _))
        ctx.pair.char₁ h₁ h
    · exact key T₂ ctx.pair.ne_bot₂ ctx.pair.le₂ ctx.pair.char₂ h₂ h

end GLevel2

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem core1517_gen (hK518 : K518) (hK517 : K517_6) (hK89 : K89Sp) (hK3 : K3DvdL3)
    (hKSML3 : KSML3) (hK4143 : K4143) (hD : K421Data) (hN : K421NonTransLin) (hKSM : KSMOdd)
    (hRank : LieOddRankChev) (hOutLin : KOutLin) (hK517a : K517_4a)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO812 : O812sixAt G M) (hO1517 : O1517bAt G M) (hO1521 : O1521At G M)
    (hO1521b : O1521bAt G M) (ctx : S15CtxGen G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    {p : ℕ} (hp : p ∈ sigmaM G M)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hbad : Bad1517 p ↥Ls) : False := by
  have hp5 : 5 ≤ p := five_le_of_mem_sigmaM h11 hp
  have hpp : p.Prime := sigmaA_prime p hp.1
  obtain ⟨hout, hX3, hnt⟩ := xlevel_out1517_gen hK4143 hD hN hKSM hRank hOutLin ctx.gn
    hpp hp5 (ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h11) (ctx.three_le p hp) hLs.1 hL
    hbad
  have hstrong3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M :=
    strong_three_of_out1517_gen hO812 hO1517 ctx hp hp5 hout
      (three_dvd_card_of_pRank (by omega))
  have hT₁ : T₁ ≠ ⊥ ∧ T₁ ≤ T.subgroupOf M ∧ (T₁.subgroupOf (T.subgroupOf M)).Characteristic :=
    ⟨ctx.pair.ne_bot₁, ctx.pair.le_center.trans (omegaOneCenterOf_le_subgroup _), ctx.pair.char₁⟩
  have hT₂ : T₂ ≠ ⊥ ∧ T₂ ≤ T.subgroupOf M ∧ (T₂.subgroupOf (T.subgroupOf M)).Characteristic :=
    ⟨ctx.pair.ne_bot₂, ctx.pair.le₂, ctx.pair.char₂⟩
  have hbad' := hbad
  have hrk : CFSG.Open.pRank 3 (Subgroup.normalizer (T₁ : Set ↥M)) ≤ 1 ∧
      CFSG.Open.pRank 3 (Subgroup.normalizer (T₂ : Set ↥M)) ≤ 1 := by
    rcases hbad with ⟨hlin, -⟩ | hsp | hom
    · have hno : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 →
          ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → E ≤ H → H = M :=
        fun E hE hEab hE9 H hH hEH =>
          eq_of_maxTwoLocal_of_nonTrans_gen hO1521 h11 hstrong3 (hnt hlin) hE hEab hE9 hH hEH
      exact ⟨pRank_normalizer_le_one_of_unique_gen ctx hno hT₁.1 hT₁.2.1 hT₁.2.2,
        pRank_normalizer_le_one_of_unique_gen ctx hno hT₂.1 hT₂.2.1 hT₂.2.2⟩
    · obtain ⟨d₁, d₂⟩ := dvd_card_normalizer_of_spom hK517a ctx.gn (S15CtxGen.good ctx) hLs hpp
        (Or.inl hsp)
      exact ⟨pRank_normalizer_le_one_of_O1521b_gen hO1521b ctx h11 hstrong3 hp hT₁.1 hT₁.2.1
          hT₁.2.2 d₁,
        pRank_normalizer_le_one_of_O1521b_gen hO1521b ctx h11 hstrong3 hp hT₂.1 hT₂.2.1 hT₂.2.2
          d₂⟩
    · obtain ⟨d₁, d₂⟩ := dvd_card_normalizer_of_spom hK517a ctx.gn (S15CtxGen.good ctx) hLs hpp
        (Or.inr hom)
      exact ⟨pRank_normalizer_le_one_of_O1521b_gen hO1521b ctx h11 hstrong3 hp hT₁.1 hT₁.2.1
          hT₁.2.2 d₁,
        pRank_normalizer_le_one_of_O1521b_gen hO1521b ctx h11 hstrong3 hp hT₂.1 hT₂.2.1 hT₂.2.2
          d₂⟩
  exact false_of_strong_three_core_gen hK518 hK517 hK89 hK3 hKSML3 ctx hstrong3 hrk.1 hrk.2 hX3.ge
    hLs hL (not_isUFourOdd_of_bad hbad')

theorem row1517_gen (hK518 : K518) (hK517 : K517_6) (hK89 : K89Sp) (hK3 : K3DvdL3)
    (hKSML3 : KSML3) (hK4143 : K4143) (hD : K421Data) (hN : K421NonTransLin) (hKSM : KSMOdd)
    (hRank : LieOddRankChev) (hOutLin : KOutLin) (hK517a : K517_4a)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO812 : O812sixAt G M) (hO1517 : O1517bAt G M) (hO1521 : O1521At G M)
    (hO1521b : O1521bAt G M) (ctx : S15CtxGen G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) :
    Row1517 G M T T₁ T₂ :=
  row1517_of_core fun _ hp _ _ hLs hL hbad =>
    core1517_gen hK518 hK517 hK89 hK3 hKSML3 hK4143 hD hN hKSM hRank hOutLin hK517a hO812 hO1517
      hO1521 hO1521b ctx h11 hp hLs hL hbad

theorem row1517 (hK518 : K518) (hK517 : K517_6) (hK89 : K89Sp) (hK3 : K3DvdL3) (hKSML3 : KSML3)
    (hK4143 : K4143) (hD : K421Data) (hN : K421NonTransLin) (hKSM : KSMOdd)
    (hRank : LieOddRankChev) (hOutLin : KOutLin) (hK517a : K517_4a)
    (hO812 : O812six) (hO1517 : O1517b) (hO1521 : O1521) (hO1521b : O1521b)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) : Row1517 G M T T₁ T₂ :=
  row1517_gen hK518 hK517 hK89 hK3 hKSML3 hK4143 hD hN hKSM hRank hOutLin hK517a
    (O812sixAt.of_ctx2 hO812 ctx) (O1517bAt.of_ctx2 hO1517 ctx) (O1521At.of_ctx2 hO1521 ctx)
    (O1521bAt.of_ctx2 hO1521b ctx) (S15CtxGen.of_ctx2 ctx) h11

end CFSG.LocalAnalysis.RankThreeUC.S15
