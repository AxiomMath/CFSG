module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCG2SylA
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCG2SylB
import CFSG.Walter.Ree.Cyclic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LieType.Ree.SmallReeModelSchreier

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

section


theorem exists_reeGamma_G2_of_model {G : Type} [Group G] {p f : ℕ}
    (h : ReeTitsModel G .twistedG2 p f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.G2.prime),
      1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card K = 3 ^ f ∧ Nonempty (G ≃* ReeTag.G2.reeGamma K a) := by
  obtain ⟨-, -, hp3, -, hiso⟩ := small_Ree_model_Schreier G p f h
  subst hp3
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  exact ⟨a, K, inferInstance, inferInstance, inferInstance, by omega, hfa, hK, hiso a K hfa hK ⟨e⟩⟩

theorem pRank_le_one_reeGamma_G2 (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup (ReeTag.G2.reeGamma K a)) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ReeTag.G2.reeGamma K a) := Subtype.finite
  refine CFSG.QuasithinUnique.Id2519.pRank_le_one_of_sylow_cyclic hp fun P => ?_
  have hq1 : 1 ≤ Nat.card K := by rw [hK]; exact Nat.one_le_pow _ _ (by norm_num)
  have hpq : ¬ p ∣ Nat.card K := fun h => by
    have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (hK ▸ h)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  by_cases h1 : p ∣ Nat.card K - 1
  · exact reeG2_sylow_cyclic_of_dvd_sub_one a ha K hK p hp5 h1 P
  by_cases h2 : p ∣ Nat.card K + 1
  · exact reeG2_sylow_cyclic_of_dvd_add_one a ha K hK p hp5 h2 P
  by_cases h3 : p ∣ Nat.card K ^ 2 - Nat.card K + 1
  · exact CFSG.Walter.Ree.reeGamma_isCyclic_sylow a ha K hK p h3 P
  have hcard := CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq (a := a) (K := K) hK
  have hndvd : ¬ p ∣ Nat.card (ReeTag.G2.reeGamma K a) := by
    rw [hcard, ← hK]
    intro h
    set q := Nat.card K with hq
    have hq2 : q ≤ q ^ 2 := by nlinarith
    have hfac : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
      zify [hq2]
      ring
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hpq (hp.dvd_of_dvd_pow h)
      · rw [hfac] at h
        rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact h2 h
        · exact h3 h
    · exact h1 h
  have hP : Nat.card P = 1 := by
    rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
  haveI : Subsingleton (P : Subgroup (ReeTag.G2.reeGamma K a)) := (Nat.card_eq_one_iff_unique.1 hP).1
  exact isCyclic_of_subsingleton

open CFSG.HardMathSupport.Lang.Coordinator in
theorem outerFixedRankCrossAt_twistedG2 : OuterFixedRankCrossAt .twistedG2 := by
  intro X _ _ n ℓ f hadm hmodel hT p hp hp5 hne hdiv α hαp hαin hrk
  exfalso
  have hR : ReeTitsModel X .twistedG2 ℓ f :=
    ((CFSG.Blueprint.LieModel.reeTitsModel hmodel (by decide)).2)
  obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨e⟩⟩ := exists_reeGamma_G2_of_model hR
  obtain ⟨-, -, hℓ3, -⟩ := small_Ree_model_Schreier X ℓ f hR
  subst hℓ3
  have hK : Nat.card K = 3 ^ (2 * a + 1) := by rw [hKcard, hfa]
  have := pRank_le_one_reeGamma_G2 a ha K hK hp hp5
  have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
