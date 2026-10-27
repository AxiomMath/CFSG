module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1517bBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open

namespace O1517b

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_isPConstrained_of_inf {M R H P : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M) (hΓ : CFSG.Open.rankThreeGamma 2 3 R ≤ M)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (M ⊓ H)) (hP3 : 3 ≤ CFSG.Open.pRank 3 P)
    (hH : CFSG.ABGLocalTools.IsPConstrained 3 ↥H) : H ≤ M := by
  have hPM : P ≤ M := hP.le.trans inf_le_left
  have hPH : P ≤ H := hP.le.trans inf_le_right
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEP, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 3) hP3
  have hE27 : Nat.card E = 27 := by simpa using hEcard
  exact le_of_isPConstrained_of_three_le_pRank hR hΓ
    (isSylowOf_of_isSylowOf_inf hR hΓ hP (by omega)) hPM hP3 hH
    (relPPrimeCore_le_of_two_le_pRank hR hΓ (hEP.trans hPM) (hEP.trans hPH) hE hE27)

end O1517b

@[expose] def O1517bRes : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ p ∈ sigmaM G M, 5 ≤ p →
        ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M → rankThreeGamma 2 3 R ≤ M →
          ∀ A : Subgroup G, A ≤ M → Nat.card A = 3 →
            p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (A : Set G)) →
            ∀ P : Subgroup G,
              CFSG.ABGLocalTools.IsSylowOf 3 P (M ⊓ Subgroup.normalizer (A : Set G)) →
              (((IsElemAbelian 3 P ∧ Nat.card P = 27) ∨ IsCyclic ↥(Subgroup.center ↥P)) ∧
                3 ≤ CFSG.Open.pRank 3 P) →
              ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.normalizer (A : Set G)) →
              Subgroup.normalizer (A : Set G) ≤ M

theorem o1517b_of_res (h : O1517bRes) : O1517b := by
  intro G _ _ hS hUC M hM hwit hstrong p hp R hR hΓ A hAM hA hpdvd P hP hshape
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  by_cases hp3 : p = 3
  · subst hp3
    have hA1 : A ≠ ⊥ := by
      rintro rfl
      simp at hA
    have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
    exact (hstrong 3 hp).normalizer_le hA1 hAp hAM
  · have hp5 : 5 ≤ p := by
      by_contra hlt
      have h2le := hpp.two_le
      have h5 : p < 5 := by omega
      interval_cases p
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hpp (by decide)
    by_cases hH : CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.normalizer (A : Set G))
    · exact O1517b.le_of_isPConstrained_of_inf hR hΓ hP hshape.2 hH
    · exact h G hS hUC M hM hwit hstrong p hp hp5 R hR hΓ A hAM hA hpdvd P hP hshape hH

end CFSG.LocalAnalysis.RankThreeUC.S15
