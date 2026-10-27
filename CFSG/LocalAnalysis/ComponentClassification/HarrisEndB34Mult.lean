module

public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPSLCover

public section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup CFSG.LieType.Steinberg.CentralExt CFSG.Blueprint.Multiplier

theorem table_order_psl_two_dvd_two {p f : ℕ} (h9 : p ^ f ≠ 9) :
    (genericOrders .PSL 2 p f).1 * (genericOrders .PSL 2 p f).2 *
      ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) ∣ 2 := by
  rw [show genericOrders .PSL 2 p f = (Nat.gcd 2 (p ^ f - 1), 1) from rfl, mul_one]
  by_cases h22 : p = 2 ∧ f = 2
  · obtain ⟨rfl, rfl⟩ := h22
    decide
  · have h32 : ¬ (p = 3 ∧ f = 2) := by
      rintro ⟨rfl, rfl⟩
      exact h9 rfl
    have hE : exceptionalOrders .PSL 2 p f = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all
    rw [hE, mul_one, mul_one]
    exact Nat.gcd_dvd_left 2 _

theorem pPrimeCore_eq_bot_of_le_center_psl_two
    {J : Type} [Group J] [Finite J] (hJ : Group.IsPerfect J) (hO : pPrimeCore 2 J ≤ center J)
    {p f : ℕ} (hm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) (h9 : p ^ f ≠ 9) :
    pPrimeCore 2 J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect J := hJ
  have hker : (QuotientGroup.mk' (pPrimeCore 2 J)).ker ≤ center J := by
    rw [QuotientGroup.ker_mk']
    exact hO
  obtain ⟨-, ⟨e⟩⟩ := GriessClassical.griess_classical_of_large .PSL
    (TBLit.models_lieModel_of_lieModel_psl_two hm) (Or.inl rfl)
  have hdvd := Subgroup.card_dvd_of_surjective
    (RankThree.PerfectCover.hopfMultiplierToKer_surjective (QuotientGroup.mk' (pPrimeCore 2 J))
      (QuotientGroup.mk'_surjective _) hker)
  rw [QuotientGroup.ker_mk', ← Nat.card_congr
    (RankThree.PerfectCover.hopfMultiplierEquivGriess (J ⧸ pPrimeCore 2 J)).toEquiv,
    Nat.card_congr e.toEquiv] at hdvd
  simp only [generic, exceptional, Nat.card_prod] at hdvd
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, Nat.card_zmod] at hdvd
  have h1 : Nat.card (pPrimeCore 2 J) = 1 :=
    Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := J)).symm
      (hdvd.trans (table_order_psl_two_dvd_two h9))
  exact Subgroup.card_eq_one.mp h1

end CFSG.ComponentClassification.HarrisLit.EndB
