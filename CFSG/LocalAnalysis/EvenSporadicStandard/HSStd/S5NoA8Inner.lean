module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerRestOfB4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.AssemblyPartial
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7LieSimple
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv13
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerComponent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerRestOfE1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S12
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S15
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S4

public section

namespace CFSG.EvenSporadicStandard.HSStd.NoA8

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

theorem innerD8ConfigC_of_steps
    (h0 : StepS0) (h2 : StepS2) (h3 : StepS3) (h4 : StepS4) (h5 : StepS5) (h6 : StepS6)
    (h7 : StepS7) (h8 : StepS8) (h9 : StepS9) (h10 : StepS10) (h11 : StepS11) (h12 : StepS12)
    (h14 : StepS14) (h15 : StepS15) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : HSLemma21Setting G L) (hG : CFSG.EvenSporadicStandard.Induction.Balance.UHered G)
    {t : G} (htL : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G}
    {z n : G} (hf : HSFusionData L t S z n) {E : Subgroup G} (hEL : E ≤ L) (hzE : z ∈ E)
    (hEab : IsElemAbelian 2 E) (hE16 : Nat.card E = 16)
    (hφ : ∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
      φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L))
    (htr : ∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e)
    (hfus : ∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G),
      m * t * m⁻¹ = t * e)
    {W : Subgroup G} (hWN : W ≤ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G))
    (hWn : ∀ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), ∀ w ∈ W, m * w * m⁻¹ ∈ W)
    (hEW : E ≤ W) (htW : t ∉ W) (hWab : IsElemAbelian 2 W) (hW : Nat.card W = 256)
    (hN : Nat.card (normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) = 16 * 23040)
    (hC : centralizer ((zpowers t ⊔ E : Subgroup G) : Set G) = zpowers t ⊔ E) :
    Nonempty (Zassenhaus.InnerD8ConfigC L t) := by
  have hb : PAB G L t E W z :=
    PAB.of_hyps hset htL ht2 hin hf hEL hzE hEab hE16 hφ htr hfus hWN hWn hEW htW hWab hW hN hC
  obtain ⟨a0⟩ := h0 G L t E W z hb
  obtain ⟨a2⟩ := h2 G L t E W z hb a0
  obtain ⟨a3⟩ := h3 G L t E W z hb a2
  obtain ⟨a4⟩ := h4 G L t E W z hb a3
  obtain ⟨a5⟩ := h5 G L t E W z hb a4
  obtain ⟨a6⟩ := h6 G L t E W z hb a5
  obtain ⟨a7⟩ := h7 G L t E W z hG hb a6
  obtain ⟨a8⟩ := h8 G L t E W z hb a7
  obtain ⟨a9⟩ := h9 G L t E W z hb a8
  obtain ⟨a10⟩ := h10 G L t E W z hb a9
  obtain ⟨a11⟩ := h11 G L t E W z hb a10
  obtain ⟨a12⟩ := h12 G L t E W z hb a11
  obtain ⟨a14⟩ := h14 G L t E W z hb a12
  exact PA14.nonempty_configC hb a14 (h15 G L t E W z hb a14)

theorem exists_maximalF_hs_of_configC
    (hB4 : Zassenhaus.HSInnerB4) (hON : Zassenhaus.ONan77S5) (hIn : Zassenhaus.ONanInspection)
    {G : Type} [Group G] [Finite G]
    (h15 : FS79Lemma15Sec G) (hKG : Zassenhaus.KGHS3) (h13 : FS79Thm13UseSec G)
    (hF1 : ∀ {α β : MulAut (alternatingGroup (Fin 6))}, α * α = 1 → β * β = 1 →
      α ∉ Zassenhaus.innR → β ∉ Zassenhaus.innR → (∃ a, orderOf a = 3 ∧ α a = a) →
      (∀ a, orderOf a = 3 → β a ≠ a) → α * β ∉ Zassenhaus.innR)
    {L : Subgroup G} (hset : HSLemma21Setting G L) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) (c : Zassenhaus.InnerD8ConfigC L t) :
    ∃ M : Subgroup G, MaximalF M ∧ IsSporadic ↥M .HS ∧
      2 ≤ Open.pRank 2 (centralizer (M : Set G)) := by
  obtain ⟨x, M, hx, hcomp, hq, hrk, h3⟩ := Zassenhaus.asm_core hset htL ht2 hin hf c
    (hB4 G L hset t htL ht2 hin S z n hf c) hON hIn h15 hKG hF1
  obtain ⟨e⟩ := hq
  have hZ := center_eq_bot_of_isSporadic_hs ⟨e⟩
  have hMq : IsSporadic (↥M ⧸ center ↥M) .HS :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  refine ⟨M, ?_, ⟨e⟩, hrk⟩
  exact Zassenhaus.maximalF_of_catalog h13 hset.1.fStarSimple hset.1.kProper hset.1.simple
    hset.1.nonabelian h3 hKG ⟨x, hx, hcomp⟩ hMq
    (fun K hKq => Zassenhaus.pRank_ne_one_of_hsType hKq)

theorem false_of_maximalF_isSporadic_hs
    {G : Type} [Group G] [Finite G] (h13 : FS79Thm13UseSec G)
    (h38 : ComponentClassification.RankTwoSporadic.SporadicCaseOdd .HS) {L : Subgroup G}
    (hStd : StdHyp G L) {M : Subgroup G} (hmax : MaximalF M)
    (hM : IsSporadic ↥M .HS) (hrk : 2 ≤ Open.pRank 2 (centralizer (M : Set G))) : False := by
  obtain ⟨e⟩ := hM
  have h4 := Zassenhaus.four_le_pRank_of_isSporadic_hs ⟨e⟩
  have hZ := center_eq_bot_of_isSporadic_hs ⟨e⟩
  have hq : IsSporadic (↥M ⧸ center ↥M) .HS :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact Zassenhaus.false_of_maximalF_hs h13 h38 hStd hmax hq (by omega) hrk

theorem hsInnerRest_of_catalog'
    (hHar : Harada39One) (hHs : Harris311) (hHiS : Harris311HiS) (hOv : HaradaOvergroups)
    (hL34 : HaradaL34Data) (h7c : ThreeCentralizer7) (hKG6 : KGA6Sq) (hON : Zassenhaus.ONan77S5)
    (hNo : ONanNoSL29Y) (hU : U43Config) (hL : HarrisL39L43NoD8) (hCov : U43CoverOrbit)
    (hC : Zassenhaus.CatE16) (hIn : Zassenhaus.ONanInspection)
    (h15 : FS79Lemma15Hered) (hKG : Zassenhaus.KGHS3) (h13 : FS79Thm13UseHered)
    (h38 : ComponentClassification.RankTwoSporadic.SporadicCaseOdd .HS) : NoA8.HSInnerRest := by
  intro G _ _ L hset hH t htL ht2 hin _
  obtain ⟨S, z, n, hf⟩ := (sylowFusion_iff L t).1 (hset.2.2.2.1 t htL ht2)
  obtain ⟨E, hEL, hzE, hEab, hE16, hφ, htr, hfus, W, -, hWN, hWn, hEW, htW, hWab, hW, hN, hCE⟩ :=
    Zassenhaus.hsInner_I1_I2 hset.2.1 htL ht2 hin hf
  obtain ⟨c⟩ := innerD8ConfigC_of_steps s0 s2 (s3 hHar hHs hOv hL34 h7c fusionA_proved) s4
    (s5 s5FusionA_proved s5FusionB_proved) s6 (s7 hHs hU hL hCov s7_lieModelSimpleU43 h15)
    (s8 hKG6) (s9 hHiS) (s10 hHiS) s11 s12 (s14 hON hNo) s15 hset hH.uHered htL ht2 hin hf hEL hzE
    hEab hE16 hφ htr hfus hWN hWn hEW htW hWab hW hN hCE
  obtain ⟨M, hmax, hM, hrk⟩ := exists_maximalF_hs_of_configC (Zassenhaus.hsInnerB4 hC) hON hIn
    (h15.sec hH.uHered) hKG (h13.sec hH.uHered)
    (fun h1 h2 h3 h4 h5 h6 => Zassenhaus.mul_not_mem_inner_of_types h1 h2 h3 h4 h5 h6)
    hset htL ht2 hin hf c
  exact false_of_maximalF_isSporadic_hs (h13.sec hH.uHered) h38 hset.1 hmax hM hrk

end CFSG.EvenSporadicStandard.HSStd.NoA8
