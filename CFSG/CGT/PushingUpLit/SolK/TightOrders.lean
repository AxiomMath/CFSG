module

public import CFSG.CGT.PushingUpLit.SolK.Tight
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.LieType.Chevalley.ExactG2FiniteOrder
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.StatedClassicalOrders
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly.LowTwoRank

theorem card_le_sixty_four_of_not_dvd {G : Type} [Group G] [Finite G] (hN : ¬ 128 ∣ Nat.card G)
    {P : Subgroup G} (hP : IsPGroup 2 P) : Nat.card P ≤ 64 := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card P ∣ Nat.card G := Subgroup.card_subgroup_dvd_card P
  by_contra hlt
  push Not at hlt
  have hm7 : 7 ≤ m := by
    by_contra hm6
    have : 2 ^ m ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  apply hN
  refine dvd_trans ?_ hdvd
  rw [hm]
  exact pow_dvd_pow 2 hm7

theorem card_of_psl_three {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .PSL 3 p f) :
    Nat.card X = ((p ^ f) ^ (3 * (3 - 1) / 2) * ∏ index ∈ Finset.Icc 2 3, ((p ^ f) ^ index - 1)) /
      Nat.gcd 3 (p ^ f - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) h

theorem card_of_psu_three_three' {X : Type} [Group X] (h : StatedClassicalModel X .PSU 3 3 1) :
    Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem tightSmallGroupOrders :
    TightSmallGroupOrders := by
  intro G _ _ h P hP
  refine card_le_sixty_four_of_not_dvd ?_ hP
  rcases h with h | h | h | h | h | h
  · rw [card_of_psl_three h]
    decide
  · rw [card_of_psu_three_three' h]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    change ¬ 128 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M11
    rw [CFSG.Sporadic.Mathieu.card_M11]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    change ¬ 128 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M12
    rw [CFSG.Sporadic.Mathieu.card_M12]
    decide
  · rcases h with ⟨ht, -⟩ | ⟨-, -, hmodel⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
      have hKcard : Nat.card K = 3 := by simpa using hK
      have h1 := (CFSG.LieType.Chevalley.exact_G2_finite_order K hKcard).2.1
      have hcen := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field .G2 K
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K))
      have hc1 :
          Nat.card ↥(Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) = 1 := by
        rw [hcen, Subgroup.card_bot]
      rw [hc1, mul_one] at h2
      rw [Nat.card_congr e.toEquiv]
      change ¬ 128 ∣ Nat.card (CFSG.Blueprint.AdjointQuotient .G2 K)
      rw [← h2, h1]
      decide
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  · rw [card_of_psl_three h]
    decide

end CFSG.CGT.PushingUpLit.SolK
