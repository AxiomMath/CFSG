module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2TriD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2TwE6Holds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.Assembly CFSG.LieType.BorelTits


theorem twoRankLow_triD4_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .triD4) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .triD4 := ht
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeTwisted] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨-, hna, ⟨θ⟩⟩ := hQ
  have hK' : Nat.card K = 2 ^ (3 * n) := by
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
  have hexp : (2 ^ n) * ((2 ^ n) * (2 ^ n)) = Nat.card K := by
    rw [hK']
    ring
  have hσ3 : ∀ c, σ (σ (σ c)) = c := by
    intro c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, hexp]
    exact pow_natCard_eq' c
  have hbig : 2 < Nat.card K := by
    rw [hK']
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨u, hu⟩ := exists_sq_ne_one K hbig
  have e0 : LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n) ≃*
      DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ) :=
    (CFSG.StandardType.centerQuot_twistedH_equiv K TwistTag.D4 n σ hσ).some
  haveI : Finite (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) :=
    Finite.of_equiv _ θ.toEquiv
  haveI : Finite (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ)) :=
    Finite.of_equiv _ e0.toEquiv
  rw [CFSG.LocalAnalysis.GLTheoremA.I107L.pRank_eq_of_quotient θ hna,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e0,
    CFSG.SectionRank.pRank_twistedDerivedQuotient (p := 2) σ hσsurj
      (d4_U_le_twistDerived hσsurj hσ3 hu)]
  exact triD4_rank hK' σ hσ hσsurj hσ3 ⟨u, hu⟩

end CFSG.LocalAnalysis.GLTheoremA.I107X2

end
