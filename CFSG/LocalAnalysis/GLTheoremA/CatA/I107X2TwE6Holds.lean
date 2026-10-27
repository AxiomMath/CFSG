module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2TwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2F4
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.Assembly CFSG.LieType.BorelTits


theorem pow_natCard_eq' {K : Type} [Field K] [Finite K] (c : K) : c ^ Nat.card K = c := by
  haveI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

theorem twoRankLow_twE6_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .twE6) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .twE6 := ht
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeTwisted] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨-, hna, ⟨θ⟩⟩ := hQ
  have hK' : Nat.card K = 2 ^ (2 * n) := by
    rw [hK, ← pow_mul, mul_comm]
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have h1 := Finite.one_lt_card (α := K)
      rw [hK', h] at h1
      simp at h1
    · exact h
  haveI : CharP K 2 := charP_two_of_card' hK'
  let σ : K →+* K := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => rfl
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hσ2 : ∀ c, σ (σ c) = c := by
    intro c
    rw [hσ, hσ, ← pow_mul, ← pow_add, show n + n = 2 * n by ring, ← hK']
    exact pow_natCard_eq' c
  have hbig : 2 < Nat.card K := by
    rw [hK']
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨u, hu⟩ := exists_sq_ne_one K hbig
  have e0 : LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) ≃*
      DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ) :=
    (CFSG.StandardType.centerQuot_twistedH_equiv K TwistTag.E6 n σ hσ).some
  haveI : Finite (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
    Finite.of_equiv _ θ.toEquiv
  haveI : Finite (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ)) :=
    Finite.of_equiv _ e0.toEquiv
  rw [CFSG.LocalAnalysis.GLTheoremA.I107L.pRank_eq_of_quotient θ hna,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e0,
    CFSG.SectionRank.pRank_twistedDerivedQuotient (p := 2) σ hσsurj
      (e6_U_le_twistDerived hσsurj hσ2 hu)]
  exact twE6_rank hK' σ hσ hσsurj hσ2 ⟨u, hu⟩

end CFSG.LocalAnalysis.GLTheoremA.I107X2

end
