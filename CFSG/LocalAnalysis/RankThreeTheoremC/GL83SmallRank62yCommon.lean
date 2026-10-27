module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Faithful
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T : Subgroup G}

theorem Prop627Failure.prime (hf : Prop627Failure G p P M x z T) : p.Prime :=
  sigmaA_prime p hf.situation.mem_sigmaA

theorem Prop627Failure.ne_two (hf : Prop627Failure G p P M x z T) : p ≠ 2 :=
  sigmaA_odd p hf.situation.mem_sigmaA

theorem Prop627Failure.sylow_le (hS : Setting G) (hf : Prop627Failure G p P M x z T) :
    (P : Subgroup G) ≤ M :=
  (sylow_le_of_isCoreMaxLocal hS hf.situation.mem_sigmaA hf.situation.isCoreMaxLocal).1

theorem Prop627Failure.B_le_P (hf : Prop627Failure G p P M x z T) :
    zpowers x ⊔ zpowers z ≤ (P : Subgroup G) :=
  sup_le (zpowers_le.mpr hf.point.mem) (zpowers_le.mpr hf.central.mem)

theorem Prop627Failure.B_le_M (hS : Setting G) (hf : Prop627Failure G p P M x z T) :
    zpowers x ⊔ zpowers z ≤ M :=
  hf.B_le_P.trans (hf.sylow_le hS)

theorem Prop627Failure.T_le_M (hf : Prop627Failure G p P M x z T) : T ≤ M :=
  hf.sylowTwo.le_core.trans (sSup_le fun _ hK => hK.1)

theorem Prop627Failure.S_le_M (hf : Prop627Failure G p P M x z T) : smallRankS x T ≤ M :=
  inf_le_left.trans hf.T_le_M

theorem Prop627Failure.S_isPGroup (hf : Prop627Failure G p P M x z T) :
    IsPGroup 2 (smallRankS x T) :=
  hf.sylowTwo.isPGroup.to_le inf_le_left

theorem Prop627Failure.z_le_normalizer_S (hf : Prop627Failure G p P M x z T) :
    zpowers z ≤ normalizer (smallRankS x T : Set G) := by
  have hzx : z ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hf.central.centralizes x
      hf.point.mem).symm
  rw [zpowers_le]
  exact inf_normalizer_le_normalizer_inf ⟨hf.sylowTwo.normalized hf.central.mem,
    le_normalizer hzx⟩

theorem Prop627Failure.B_le_normalizer_S (hf : Prop627Failure G p P M x z T) :
    zpowers x ⊔ zpowers z ≤ normalizer (smallRankS x T : Set G) := by
  have hxx : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  refine sup_le ?_ hf.z_le_normalizer_S
  rw [zpowers_le]
  exact inf_normalizer_le_normalizer_inf ⟨hf.sylowTwo.normalized hf.point.mem,
    le_normalizer hxx⟩

theorem Prop627Failure.R_ne_bot (hS : Setting G) (hf : Prop627Failure G p P M x z T) :
    smallRankR x z T ≠ ⊥ := by
  obtain ⟨v, hv, hzv⟩ := exists_mem_inf_centralizer_not_commute hS hf.situation hf.point
    hf.central hf.sylowTwo
  intro hbot
  have hle : zpowers z ≤ centralizer ((smallRankS x T : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  exact hzv (mem_centralizer_iff.mp (hle (mem_zpowers z)) v hv).symm

theorem Prop627Failure.S_ne_bot (hS : Setting G) (hf : Prop627Failure G p P M x z T) :
    smallRankS x T ≠ ⊥ := by
  obtain ⟨v, hv, hzv⟩ := exists_mem_inf_centralizer_not_commute hS hf.situation hf.point
    hf.central hf.sylowTwo
  intro hbot
  have hv1 : v = 1 := Subgroup.mem_bot.mp (hbot ▸ hv)
  exact hzv (by rw [hv1, mul_one, one_mul])

theorem Prop627Failure.normalizer_zpowers_le (hS : Setting G)
    (hf : Prop627Failure G p P M x z T) : normalizer (zpowers z : Set G) ≤ M :=
  normalizer_zpowers_le_of_largeObstruction_empty hS hf.situation.mem_sigmaA
    hf.situation.isCoreMaxLocal hf.situation.largeObstruction_empty hf.central.mem
    hf.central.centralizes hf.central.ne_one hf.central.pow_eq_one

theorem Prop627Failure.pCoreOf_two_le_T (hf : Prop627Failure G p P M x z T) :
    pCoreOf 2 M ≤ T := by
  have hp := hf.prime
  have hT := hf.sylowTwo
  have hN2 : IsPGroup 2 (pCoreOf 2 M) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 M
  have hNM : pCoreOf 2 M ≤ M := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 M
  have hnorm : ((pCoreOf 2 M).subgroupOf M).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 M M le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hMN : M ≤ normalizer (pCoreOf 2 M : Set G) := le_normalizer_of_normal_subgroupOf hNM
  have hKM : rankThreePrimeCore p M ≤ M := sSup_le fun _ hK => hK.1
  have hcop : p.Coprime (Nat.card (pCoreOf 2 M)) := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hf.ne_two)
  have hNK : pCoreOf 2 M ≤ rankThreePrimeCore p M :=
    le_sSup ⟨hNM, normal_subgroupOf_of_le_normalizer hMN, hcop⟩
  have hTK : IsPGroup 2 (T.subgroupOf (rankThreePrimeCore p M)) :=
    hT.isPGroup.of_equiv (subgroupOfEquivOfLe hT.le_core).symm
  have : (pCoreOf 2 M |>.subgroupOf (rankThreePrimeCore p M)).Normal :=
    normal_subgroupOf_of_le_normalizer (hKM.trans hMN)
  have hle := (hN2.of_equiv (subgroupOfEquivOfLe hNK).symm).le_sylow_of_normal
    (hTK.toSylow hT.index_odd)
  intro n hn
  have hmem : (⟨n, hNK hn⟩ : rankThreePrimeCore p M) ∈
      (pCoreOf 2 M).subgroupOf (rankThreePrimeCore p M) := mem_subgroupOf.mpr hn
  exact mem_subgroupOf.mp (hle hmem)

end CFSG.LocalAnalysis.RankThreeTheoremC
