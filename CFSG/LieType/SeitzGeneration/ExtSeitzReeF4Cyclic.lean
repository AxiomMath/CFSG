module

public import CFSG.RankThree.PartOne.SEITZX.ReeSplit
public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)



theorem extSeitzAtInnerFor_reeF4_cyclic (m : ℕ) :
    ExtSeitzAtInnerFor (.reeF4 m) fun p =>
      ¬ p ∣ 2 ^ (2 * m + 1) - 1 ∧ ¬ p ∣ 2 ^ (2 * m + 1) + 1 ∧
        ¬ p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd ⟨hP, h3, h4'⟩ E hE hcard hinner
  have : Fact p.Prime := ⟨hp⟩
  left
  exfalso
  have hinj := conj_injective_of_simple hnab
  obtain ⟨hE₁, hmap⟩ := inner_preimage_data (p := p) hinj E hinner
  set E₁ := E.comap (MulAut.conj : K →* MulAut K) with hE₁def
  have hcard₁ : Nat.card E₁ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hcard
  obtain ⟨X, _, _, _, -, hX, ⟨e⟩⟩ := CFSG.RankThree.PartOne.SEITZX.exists_reeGamma_model hiso
  have : Finite (ModGL F4.tag X) := finite_modGL
  have : Finite (F4.reeGamma X m) := Subtype.finite
  have hdvd : p ∣ Nat.card (F4.reeGamma X m) := by
    have h0 := Subgroup.card_subgroup_dvd_card E₁
    rw [hcard₁, Nat.card_congr e.toEquiv] at h0
    exact (dvd_pow_self p two_ne_zero).trans h0
  have h5 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt E₁ hE₁ hcard₁
  have h6 := CFSG.RankThree.PartOne.pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e
  rcases (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    m X hX).2 p hp (by omega) hdvd with h7 | h7 | h7 | h7 | h7
  · exact hP h7
  · exact h3 h7
  · exact h4' h7
  · have := CFSG.RankThree.PartOne.K128.pRank_le_one_ree_phi6 hX hp hp5 h7
    omega
  · have := CFSG.RankThree.PartOne.K128.pRank_le_one_ree_phi12 hX hp hp5 h7
    omega

end CFSG.LieType.SeitzGeneration
