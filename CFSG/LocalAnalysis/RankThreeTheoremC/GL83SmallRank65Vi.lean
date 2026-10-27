module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Layer
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.SignalizerFunctorTheorem.McBride.Thompson.SolvableFPF

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem vi_exists_normalized_sylow {O H : Subgroup G} (hnil : Group.IsNilpotent O)
    (hHO : H ≤ normalizer (O : Set G)) {q : ℕ} (hq : q.Prime) (hqO : q ∣ Nat.card O) :
    ∃ S : Subgroup G, S ≤ O ∧ IsPGroup q S ∧ S ≠ ⊥ ∧ H ≤ normalizer (S : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  have := hnil
  obtain ⟨K⟩ : Nonempty (Sylow q O) := inferInstance
  have : (K : Subgroup O).Characteristic := Sylow.characteristic_of_normal K inferInstance
  refine ⟨(K : Subgroup O).map O.subtype, map_subtype_le _, K.isPGroup'.map O.subtype, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ O.subtype_injective]
    exact Sylow.ne_bot_of_dvd_card K hqO
  · exact hHO.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

private theorem vi_coprime_six {q : ℕ} (n : ℕ) (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) :
    Nat.Coprime (q ^ n) 6 := by
  refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => ?_)
  rw [show (6 : ℕ) = 2 * 3 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
  · exact h3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)

theorem primeCore_le_pCoreOf_of_prop65 (hS : Setting G) (h65 : GL83SmallRankProp65 G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M)
    (he : Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))))
    {x z : G} (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H : Subgroup G}
    (hBH : zpowers x ⊔ zpowers z ≤ H) (hHM : ¬ H ≤ M) (hOM : rankThreePrimeCore 3 H ≤ M)
    {b : G} (hb : b ∈ zpowers x ⊔ zpowers z) (hbz : b ∉ zpowers z)
    (hfix : ∀ o ∈ rankThreePrimeCore 3 H, b * o = o * b → o = 1) :
    rankThreePrimeCore 3 H ≤ pCoreOf 2 H := by
  obtain ⟨hOH, hHO, hO3⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 H
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ one_mem _)
  have hord : orderOf b = 3 := orderOf_eq_prime (hB.isElemAbelian.2 b hb) hb1
  have hfix' : rankThreePrimeCore 3 H ⊓ centralizer ({b} : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun o ho => ?_
    rw [mem_bot]
    exact hfix o ho.1 (mem_centralizer_singleton_iff.1 ho.2).symm
  have hnil := CFSG.SignalizerFunctorTheorem.McBride.Thompson.fpf_nilpotent Nat.prime_three hord
    (hHO (hBH hb)) hfix'
  have hq2 : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card (rankThreePrimeCore 3 H) → q = 2 := by
    intro q hq hqO
    by_contra h2
    have h3 : q ≠ 3 := by
      rintro rfl
      exact absurd (Nat.Coprime.eq_one_of_dvd hO3 hqO) (by norm_num)
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨S, hSO, hSp, hS1, hHS⟩ := vi_exists_normalized_sylow hnil hHO hq hqO
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hSp
    have hc : Nat.Coprime (Nat.card S) 6 := hn ▸ vi_coprime_six n hq h2 h3
    exact hHM (hHS.trans (h65 P M hsit hsolv he x z hx hz S (hSO.trans hOM) hS1 hc
      (hBH.trans hHS)))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOH hHO
    (IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hq2))

theorem prop614Core19_of_core20 (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (h : GL83SmallRankProp614Core20 G) : GL83SmallRankProp614Core19 G := by
  intro P M hsit hsolv he x z hx hz H S hext h3 hHN hmax hOS hS1 hS2 hOM hex
  obtain ⟨K, b, hK, hb⟩ := hex
  exact h P M hsit hsolv he x z hx hz H S hext h3 hHN hmax hOS hS1 hS2 hOM
    (primeCore_le_pCoreOf_of_prop65 hS (prop65_of_kfacts hS hU0 hK1 hK2) hsit hsolv he hx hz
      hext.pair.le hext.pair.not_le hOM hb.mem hb.not_mem hb.fixed_point_free) ⟨K, b, hK, hb⟩

theorem prop614_of_core20 (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (hK : KFactBlockFactorThreePrime) (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (hK1 : KFactRankTwoUniqueness)
    (hK2 : KFactRankThreeStructure) (h627 : GL83SmallRankProp627 G)
    (h632 : GL83SmallRankProp632 G) (h : GL83SmallRankProp614Core20 G) :
    GL83SmallRankProp614 G :=
  prop614_of_core19 hS hU0 hD2 hK hKF1 hKF2 h627 h632 (prop614Core19_of_core20 hS hU0 hK1 hK2 h)

end CFSG.LocalAnalysis.RankThreeTheoremC
