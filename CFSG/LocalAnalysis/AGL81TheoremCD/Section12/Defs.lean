module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.HypC
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineConseq
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def weakBlockSet (M H : Subgroup G) : Set (Subgroup G) :=
  {L | IsWeakSBlock M (pCoreOf 2 H) L}

structure TwelveCtx (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H : Subgroup G) :
    Prop where
  cstar : CStarGen G
  maxLocal : rankThreeIsMaxTwoLocal M
  sigma_nonempty : (sigmaSet G M).Nonempty
  mem_QSet : Q ∈ QSet M p
  mem_H4Star : H ∈ H4StarFam p M Q

theorem mem_H2StarFam_of_le {M E Q H : Subgroup G} (hE : E ≤ Q)
    (hH : H ∈ H2StarFam M Q) : H ∈ H2StarFam M E := by
  refine ⟨⟨hH.1.1, ⟨hE.trans hH.1.2.1, hH.1.2.2.1, hH.1.2.2.2⟩⟩, fun H' hH' hHH' => ?_⟩
  exact hH.2 H' ⟨hH'.1, ⟨hH.1.2.1.trans hHH', hH'.2.2.1, hH'.2.2.2⟩⟩ hHH'

def IsSimpleOfOrder (n : ℕ) (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ¬ Group.IsSolvable X ∧ Nat.card X = n

instance primeComplementCore_normal (d : ℕ) (X : Type) [Group X] :
    (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := X) d).Normal :=
  Subgroup.normal_sSup _ fun _ h => h.1

abbrev modPrimeComplement (d : ℕ) (Y : Subgroup G) : Type :=
  ↥Y ⧸ CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d

@[expose] def jSub (M H : Subgroup G) : Subgroup G :=
  sSup (weakBlockSet M H)

theorem le_jSub {M H L : Subgroup G} (hL : L ∈ weakBlockSet M H) : L ≤ jSub M H :=
  le_sSup hL

theorem jSub_le (M H : Subgroup G) : jSub M H ≤ M :=
  sSup_le fun _ hL => hL.le

namespace TwelveCtx

variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem H_mem_H2Star (h : TwelveCtx G M p Q H) : H ∈ H2StarFam M Q := h.mem_H4Star.1

theorem H_mem_H4 (h : TwelveCtx G M p Q H) : H ∈ H4Fam p M Q := h.mem_H4Star.2

theorem H_ne_top (h : TwelveCtx G M p Q H) : H ≠ ⊤ := h.H_mem_H2Star.1.1

theorem Q_le_H (h : TwelveCtx G M p Q H) : Q ≤ H := h.H_mem_H2Star.1.2.1

theorem not_H_le_M (h : TwelveCtx G M p Q H) : ¬ H ≤ M := h.H_mem_H2Star.1.2.2.1

theorem p_prime (h : TwelveCtx G M p Q H) : p.Prime := QSet.prime_of_mem h.mem_QSet

theorem p_odd (h : TwelveCtx G M p Q H) : p ≠ 2 := QSet.ne_two_of_mem h.mem_QSet

theorem Q_le_M (h : TwelveCtx G M p Q H) : Q ≤ M := QSet.le_of_mem h.mem_QSet

theorem Q_isPGroup (h : TwelveCtx G M p Q H) : IsPGroup p Q := QSet.isPGroup_of_mem h.mem_QSet

theorem two_le_pRank (h : TwelveCtx G M p Q H) : 2 ≤ CFSG.Open.pRank p Q :=
  QSet.two_le_pRank_of_mem h.mem_QSet

theorem pCore_two_inter (h : TwelveCtx G M p Q H) :
    pCoreOf 2 H = pCoreOf 2 (H ⊓ M) := h.H_mem_H4.2.2

theorem Q_ne_bot (h : TwelveCtx G M p Q H) : Q ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨E, hEQ, hE, hEc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2) h.two_le_pRank
  intro hbot
  have hEbot : E = ⊥ := le_bot_iff.mp (hbot ▸ hEQ)
  rw [hEbot, Subgroup.card_bot] at hEc
  exact (Nat.one_lt_pow two_ne_zero h.p_prime.one_lt).ne hEc

theorem H_twoLocal (h : TwelveCtx G M p Q H) : IsTwoLocal H := by
  haveI : IsSimpleGroup G := h.cstar.simple
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section14.isTwoLocal_of_mem_H2StarFam
    h.cstar.nonab h.cstar.charTwo h.Q_ne_bot h.H_mem_H2Star

theorem p_not_mem_sigma (h : TwelveCtx G M p Q H) : p ∉ sigmaSet G M := by
  intro hpσ
  exact h.not_H_le_M (h.cstar.embed p hpσ.1 M h.maxLocal Q h.Q_le_M h.Q_isPGroup
    h.two_le_pRank H h.H_twoLocal h.Q_le_H)

theorem exists_E_sq (h : TwelveCtx G M p Q H) :
    ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      rankThreeGamma 1 p E ≤ M := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  exact QSet.exists_isElemAbelian_card_sq h.mem_QSet h.p_not_mem_sigma

theorem hypCGen {E : Subgroup G} (h : TwelveCtx G M p Q H) (hEQ : E ≤ Q)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.HypCGen G M p E H where
  cstar := h.cstar
  maxLocal := h.maxLocal
  sigma_nonempty := h.sigma_nonempty
  prime := h.p_prime
  odd := h.p_odd
  E_le_M := hEQ.trans h.Q_le_M
  elem := hE
  card := hEc
  gamma := hΓ
  mem := mem_H2StarFam_of_le hEQ h.H_mem_H2Star

end TwelveCtx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
