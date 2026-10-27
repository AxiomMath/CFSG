module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Main
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Prime
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614CE

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_two_of_forall_prime_dvd {H : Subgroup G}
    (h : ∀ f : ℕ, f.Prime → f ∣ Nat.card H → f = 2) : IsPGroup 2 H :=
  IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    (fun hf hd => h _ hf hd))

theorem pCoreOf_two_le_rankThreePrimeCore_three (N : Subgroup G) :
    pCoreOf 2 N ≤ rankThreePrimeCore 3 N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  have hnorm : ((pCoreOf 2 N).subgroupOf N).Normal := by
    have : (CFSG.Open.pCore 2 N).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    unfold pCoreOf
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
    exact this
  have h32 : Nat.Coprime 3 2 := (Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)
  exact le_sSup ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 N, hnorm, by rw [hn]; exact h32.pow_right n⟩

theorem coprime_six_of_isPGroup {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hf3 : f ≠ 3)
    {F : Subgroup G} (hF : IsPGroup f F) : Nat.Coprime (Nat.card F) 6 := by
  haveI : Fact f.Prime := ⟨hf⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hF
  rw [hn]
  refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hf).2 fun h => ?_)
  rw [show (6 : ℕ) = 2 * 3 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hf).1 h with h | h
  · exact hf2 ((Nat.prime_dvd_prime_iff_eq hf Nat.prime_two).1 h)
  · exact hf3 ((Nat.prime_dvd_prime_iff_eq hf Nat.prime_three).1 h)

theorem rankThreePrimeCore_eq_pCoreOf_two (hK1 : KFactRankTwoUniqueness)
    (hK2 : KFactRankThreeStructure) (hK : KFactBlockFactorThreePrime)
    {P : Sylow 3 G} {M : Subgroup G} {x z : G} (hsit : Sit P M x z)
    (hα : HasPrimeConstraint (G := M) 3) {N T : Subgroup G} (hloc : LocalPair M x z N T) :
    rankThreePrimeCore 3 N = pCoreOf 2 N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := hsit.setting
  have hpl := SmallRankPlane.of_situation hS hsit.situation hsit.point hsit.central
  have hB3 : IsPGroup 3 ↥(zpowers x ⊔ zpowers z) := IsPGroup.of_card (n := 2) hpl.card_eq
  have hOM : rankThreePrimeCore 3 N ≤ M :=
    primeCore_le_of_isMaxTwoInvariantIn hS hK hloc.twoLocal hB3 hloc.le hloc.maxInv
      hloc.char_le
  obtain ⟨hON, hNO, hO3⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 N
  have hOp : ¬ 3 ∣ Nat.card (rankThreePrimeCore 3 N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3
  have h2 : IsPGroup 2 (rankThreePrimeCore 3 N) := by
    refine isPGroup_two_of_forall_prime_dvd fun f hf hfO => ?_
    by_contra hf2
    have hf3 : f ≠ 3 := by
      rintro rfl
      exact hOp hfO
    haveI : Fact f.Prime := ⟨hf⟩
    have hbotf : IsPGroup f (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
    have hBbot : zpowers x ⊔ zpowers z ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    obtain ⟨F, hFsyl, -, hBF⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three hf hB3 hOp (hloc.le.trans hNO) bot_le hbotf hBbot
    have hFsyl' : CFSG.ABGLocalTools.IsSylowOf f F (rankThreePrimeCore 3 N) :=
      CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hFsyl
    have hF1 : F ≠ ⊥ := by
      obtain ⟨P2, hP2⟩ := hFsyl'
      intro hF
      have h1 := P2.not_dvd_index
      have hP2bot : (P2 : Subgroup ↥(rankThreePrimeCore 3 N)) = ⊥ := by
        rw [hF] at hP2
        exact (Subgroup.map_eq_bot_iff_of_injective _
          (rankThreePrimeCore 3 N).subtype_injective).mp hP2
      rw [hP2bot, Subgroup.index_bot] at h1
      exact h1 hfO
    have hNF : normalizer (F : Set G) ≤ M :=
      prop65Alpha_of_kfacts hS hsit.u0 hK1 hK2 P M hsit.situation hα x z hsit.point hsit.central
        F (hFsyl.1.trans hOM) hF1 (coprime_six_of_isPGroup hf hf2 hf3 hFsyl.2.1) hBF
    exact hloc.not_le ((le_sup_normalizer_of_isSylowOf hNO hFsyl').trans (sup_le hOM hNF))
  exact le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hON hNO h2)
    (pCoreOf_two_le_rankThreePrimeCore_three N)

theorem coreTwo_of_kfacts (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hK : KFactBlockFactorThreePrime) (G : Type) [Group G] [Finite G] : CoreTwo G :=
  fun _ _ _ _ hsit hα _ _ hloc => rankThreePrimeCore_eq_pCoreOf_two hK1 hK2 hK hsit hα hloc

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614CE
