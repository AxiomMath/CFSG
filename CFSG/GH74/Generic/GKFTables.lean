module

public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PerfectCover

open CFSG.ComponentClassification.TBLit in
theorem card_hopfMultiplier_of_griess (hGA : GriessMultipliersAllModels) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel X t n p f) :
    Nat.card (hopfMultiplier X) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA X t n p f hm
  rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_prod]
  unfold generic exceptional
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]

open CFSG.ComponentClassification.TBLit in
theorem noTwoCover_of_griess (hGA : GriessMultipliersAllModels) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel X t n p f)
    (h1 : Odd (genericOrders t n p f).1) (h2 : Odd (genericOrders t n p f).2)
    (h3 : Odd (exceptionalOrders t n p f).1) (h4 : Odd (exceptionalOrders t n p f).2) :
    NoTwoCover X := by
  refine noTwoCover_of_odd_hopfMultiplier ?_
  rw [card_hopfMultiplier_of_griess hGA hm]
  exact (h1.mul h2).mul (h3.mul h4)

theorem odd_gcd_of_odd_left {a b : ℕ} (ha : Odd a) : Odd (Nat.gcd a b) :=
  Odd.of_dvd_nat ha (Nat.gcd_dvd_left a b)

open CFSG.ComponentClassification.TBLit in
theorem noTwoCover_psl3_of_griess (hGA : GriessMultipliersAllModels) {p f : ℕ} (hp2 : p ≠ 2)
    {S : Type} [Group S] (hm : CFSG.Models.LieModel S .PSL 3 p f) : NoTwoCover S := by
  have hexc : exceptionalOrders .PSL 3 p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  refine noTwoCover_of_griess hGA hm ?_ ?_ ?_ ?_
  · exact odd_gcd_of_odd_left (by decide)
  · exact odd_one
  · rw [hexc]; exact odd_one
  · rw [hexc]; exact odd_one

open CFSG.ComponentClassification.TBLit in
theorem noTwoCover_psu3_of_griess (hGA : GriessMultipliersAllModels) {p f : ℕ}
    {S : Type} [Group S] (hm : CFSG.Models.LieModel S .PSU 3 p f) : NoTwoCover S := by
  have hexc : exceptionalOrders .PSU 3 p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  refine noTwoCover_of_griess hGA hm ?_ ?_ ?_ ?_
  · exact odd_gcd_of_odd_left (by decide)
  · exact odd_one
  · rw [hexc]; exact odd_one
  · rw [hexc]; exact odd_one

open CFSG.ComponentClassification.TBLit in
theorem noTwoCover_g2_of_griess (hGA : GriessMultipliersAllModels) {p f : ℕ} (hp2 : p ≠ 2)
    {S : Type} [Group S] (hm : CFSG.Models.LieModel S .G2 0 p f) : NoTwoCover S := by
  have hexc : Odd (exceptionalOrders .G2 0 p f).1 ∧ Odd (exceptionalOrders .G2 0 p f).2 := by
    unfold exceptionalOrders
    split <;> simp_all
    decide
  refine noTwoCover_of_griess hGA hm ?_ ?_ hexc.1 hexc.2
  · exact odd_one
  · exact odd_one

open CFSG.ComponentClassification.TBLit in
theorem noTwoCover_3D4_of_griess (hGA : GriessMultipliersAllModels) {p f : ℕ}
    {S : Type} [Group S] (hm : CFSG.Models.LieModel S .trialityD4 0 p f) : NoTwoCover S := by
  have hexc : exceptionalOrders .trialityD4 0 p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  refine noTwoCover_of_griess hGA hm ?_ ?_ ?_ ?_
  · exact odd_one
  · exact odd_one
  · rw [hexc]; exact odd_one
  · rw [hexc]; exact odd_one

open CFSG.ComponentClassification.TBLit in
theorem noTwoCover_ree_of_griess (hGA : GriessMultipliersAllModels) {f : ℕ}
    {S : Type} [Group S] (hm : CFSG.Models.LieModel S .twistedG2 0 3 f) : NoTwoCover S := by
  have hexc : exceptionalOrders .twistedG2 0 3 f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  refine noTwoCover_of_griess hGA hm ?_ ?_ ?_ ?_
  · exact odd_one
  · exact odd_one
  · rw [hexc]; exact odd_one
  · rw [hexc]; exact odd_one

open CFSG.ComponentClassification.TBLit in
theorem noTwoCover_psl5_of_griess (hGA : GriessMultipliersAllModels) {p f : ℕ}
    {S : Type} [Group S] (hm : CFSG.Models.LieModel S .PSL 5 p f) : NoTwoCover S := by
  have hexc : exceptionalOrders .PSL 5 p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  refine noTwoCover_of_griess hGA hm ?_ ?_ ?_ ?_
  · exact odd_gcd_of_odd_left (by decide)
  · exact odd_one
  · rw [hexc]; exact odd_one
  · rw [hexc]; exact odd_one

open CFSG.ComponentClassification.TBLit in
theorem noTwoCover_psu5_of_griess (hGA : GriessMultipliersAllModels) {p f : ℕ}
    {S : Type} [Group S] (hm : CFSG.Models.LieModel S .PSU 5 p f) : NoTwoCover S := by
  have hexc : exceptionalOrders .PSU 5 p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  refine noTwoCover_of_griess hGA hm ?_ ?_ ?_ ?_
  · exact odd_gcd_of_odd_left (by decide)
  · exact odd_one
  · rw [hexc]; exact odd_one
  · rw [hexc]; exact odd_one

end CFSG.GH74.Generic
