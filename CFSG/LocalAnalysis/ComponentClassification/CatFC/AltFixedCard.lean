module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterKGA8TAlt

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_fixedSubgroup_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 7 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} (hσ : orderOf σ = 2) :
    ∃ r : ℕ, 1 ≤ r ∧ 2 * r ≤ n ∧
      Nat.card (fixedSubgroup σ) = 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial := by
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by decide)
  obtain ⟨a, ha1, ha2, hcard⟩ :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.card_autCentralizer_alt n (by omega)
      (by omega) θ σ hσ2 hσ1
  rw [autCentralizer_eq_fixedSubgroup] at hcard
  refine ⟨a, ha1, ha2, ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h2 : 2 * Nat.card (fixedSubgroup σ) =
      2 * (2 ^ b * (b + 1).factorial * (n - 2 * (b + 1)).factorial) := by
    rw [hcard]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

end CFSG.ComponentClassification.CatFC
