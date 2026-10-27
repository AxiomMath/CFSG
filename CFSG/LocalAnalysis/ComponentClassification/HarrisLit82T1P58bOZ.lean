module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b

open CFSG Subgroup Assembly.LowTwoRank Blueprint

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem card_center_dvd_multiplier (hX : IsQuasisimple X) :
    Nat.card (center X) ∣ Nat.card (CFSG.Open.griessHopfMultiplier (X ⧸ center X)) := by
  have : Group.IsPerfect X := hX.1
  have hker : (QuotientGroup.mk' (center X)).ker ≤ center X := (QuotientGroup.ker_mk' _).le
  have hdvd := Subgroup.card_dvd_of_surjective
    (f := CFSG.RankThree.PerfectCover.hopfMultiplierToKer (QuotientGroup.mk' (center X))
      (QuotientGroup.mk'_surjective _) hker)
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective _
      (QuotientGroup.mk'_surjective _) hker)
  rwa [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
    (X ⧸ center X)).toEquiv, QuotientGroup.ker_mk'] at hdvd

theorem odd_exceptionalOrders_POmegaOdd (n p f : ℕ) :
    Odd ((Multiplier.exceptionalOrders .POmegaOdd n p f).1 *
      (Multiplier.exceptionalOrders .POmegaOdd n p f).2) := by
  by_cases h : n = 3 ∧ p = 3 ∧ f = 1
  · obtain ⟨rfl, rfl, rfl⟩ := h
    decide
  · have he : Multiplier.exceptionalOrders .POmegaOdd n p f = (1, 1) := by
      unfold Multiplier.exceptionalOrders
      split <;> simp_all
    rw [he]
    decide

theorem card_center_eq_two_of_POmegaOdd (hGA : TBLit.GriessMultipliersAllModels)
    (hX : IsQuasisimple X) (hO : pPrimeCore 2 X = ⊥) {c : X} (hc2 : orderOf c = 2)
    (hcZ : c ∈ center X) {n p f : ℕ}
    (hm : Blueprint.LieModel (X ⧸ center X) .POmegaOdd n p f) : Nat.card (center X) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod : CFSG.Models.LieModel (X ⧸ center X) .POmegaOdd n p f := by
    rcases hm with ⟨-, hc⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact ⟨hc.1, Or.inl hc⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨-, ⟨eM⟩⟩ := hGA _ .POmegaOdd n p f hmod
  have hdvd := card_center_dvd_multiplier hX
  rw [Nat.card_congr eM.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod] at hdvd
  simp only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hdvd
  have hg : Multiplier.genericOrders .POmegaOdd n p f = (2, 1) := rfl
  rw [hg] at hdvd
  have hodd := odd_exceptionalOrders_POmegaOdd n p f
  set e := (Multiplier.exceptionalOrders .POmegaOdd n p f).1 *
    (Multiplier.exceptionalOrders .POmegaOdd n p f).2 with he
  have hdvd' : Nat.card (center X) ∣ 2 * e := by
    rw [he]
    simpa [mul_assoc] using hdvd
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp (Sol78.center_isPGroup_two hO))
  have h2Z : 2 ∣ Nat.card (center X) := by
    have h1 : orderOf (⟨c, hcZ⟩ : center X) ∣ Nat.card (center X) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hc2] at h1
  rw [ha] at hdvd' h2Z ⊢
  rcases a with _ | _ | a
  · exact absurd h2Z (by norm_num)
  · rfl
  · exfalso
    have h4 : 4 ∣ 2 * e := (pow_dvd_pow 2 (by omega : 2 ≤ a + 1 + 1)).trans hdvd'
    obtain ⟨j, hj⟩ := hodd
    omega

end CFSG.ComponentClassification.HarrisLit.T1.P58b
