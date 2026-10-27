module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Local.HighRankAbelianUniquenessCentralizers
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Local.SigmaCoreNontrivial

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem prep09_hallCoreIn_eq (M : Subgroup G) : Prep09.hallCoreIn M = hallCoreIn M := by
  rw [Prep09.hallCoreIn_def, hallCoreIn_eq]

theorem natCard_hallCoreIn_eq [Finite G] (T : Subgroup G) :
    Nat.card ↥(hallCoreIn T) = Nat.card (hallCore ↥T) := by
  rw [hallCoreIn_eq, Subgroup.card_subtype]

theorem relIndex_hallCoreIn_eq [Finite G] (T : Subgroup G) :
    (hallCoreIn T).relIndex T = (hallCore ↥T).index := by
  rw [Subgroup.relIndex, subgroupOf_hallCoreIn_eq]

theorem isGreatest_isNilpotentNormalHall_hallCoreIn [Finite G] (T : Subgroup G) :
    IsGreatest {N : Subgroup G | Prep09.IsNilpotentNormalHall T N} (hallCoreIn T) := by
  constructor
  · refine ⟨hallCoreIn_le T, ?_, isNilpotent_hallCoreIn T, ?_⟩
    · rw [subgroupOf_hallCoreIn_eq]; exact hallCore_normal
    · rw [natCard_hallCoreIn_eq, relIndex_hallCoreIn_eq]
      exact coprime_natCard_index_hallCore
  · rintro N ⟨hNT, hNnormal, hNnil, hNcop⟩
    have hnil : Group.IsNilpotent ↥(N.subgroupOf T) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNT).symm
    have hcop : Nat.Coprime (Nat.card ↥(N.subgroupOf T)) (N.subgroupOf T).index := by
      rw [natCard_subgroupOf hNT]; exact hNcop
    have h := le_hallCore_of_normal_of_isNilpotent_of_coprime hNnormal hnil hcop
    have hmap := Subgroup.map_mono (f := T.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hNT, ← hallCoreIn_eq] at hmap

theorem exists_isPlaneAt_of_elementaryAbelianPRank_eq_two [Finite G] {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} (h : elementaryAbelianPRank p ↥X = 2) :
    ∃ A ≤ X, Prep08.IsPlaneAt p A := by
  obtain ⟨A, hAX, hA⟩ :=
    exists_le_nonempty_mulEquiv_of_le_elementaryAbelianPRank (d := 2) hp h.ge
  exact ⟨A, hAX, isElementaryAbelian_of_nonempty_mulEquiv_multiplicative_pi hA,
    natCard_of_nonempty_mulEquiv_multiplicative_pi hA⟩

theorem FTS_signalizer_nilpotent_supporting_core
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_signalizer_unique_supporting_maximum.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_signalizer_nilpotent_supporting_core.{u} := by
  intro G _ _ hG x hx hk T hT
  have := hG.isSimpleGroup
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, h₃T⟩ := h₃ G hG x hx hk
  obtain ⟨hRx, hRxne, hprimes, hMall⟩ := h₃T T hT.isCoatom hT.le
  obtain ⟨M, hM, hxM, hxne⟩ := mem_sigmaSupport.1 hx
  obtain ⟨p, hp, hpx⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ orderOf x := by
    have h1 : orderOf x ≠ 1 := fun h => hxne (orderOf_eq_one_iff.1 h)
    exact ⟨(orderOf x).minFac, Nat.minFac_prime h1, Nat.minFac_dvd _⟩
  obtain ⟨-, hpσ, hrank⟩ := mem_tauTwoPrimes_iff.1 (hprimes p hp hpx)
  obtain ⟨A, hAT, hAplane⟩ := exists_isPlaneAt_of_elementaryAbelianPRank_eq_two hp hrank
  obtain ⟨hnil, -, -⟩ := h₂ G hG08 T A p hT.isCoatom hp hpσ hAT hAplane
  have hHS : hallCoreIn T = sigmaCore T :=
    (hallCoreIn_eq_sigmaCore_iff_isNilpotent hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hT.isCoatom).2 hnil
  have : Fintype G := Fintype.ofFinite G
  have hSne : sigmaCore T ≠ ⊥ := (FBG_sigma_core_nontrivial h₁ G hG02 T hT.isCoatom).2
  obtain ⟨-, hxMT, hsplit, -⟩ := hMall M (mem_sigmaSupportingMaximals.2 ⟨hM, hxM⟩)
  have hxnotS : x ∉ sigmaCore T := by
    intro hxS
    have hmem : x ∈ sigmaCore T ⊓ (M ⊓ T) := ⟨hxS, hxMT⟩
    rw [hsplit.inf_eq_bot] at hmem
    exact hxne (Subgroup.mem_bot.1 hmem)
  rw [prep09_hallCoreIn_eq, hHS]
  refine ⟨hnil, rfl, hSne, ?_, hRx, hRxne, hxnotS, hxMT.2, hxnotS, hRx ▸ hRxne⟩
  rw [← hHS]
  exact isGreatest_isNilpotentNormalHall_hallCoreIn T

end

end CFSG.FeitThompson.Proofs
