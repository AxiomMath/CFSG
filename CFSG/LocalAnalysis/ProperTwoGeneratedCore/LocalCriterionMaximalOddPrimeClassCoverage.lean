module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingDatum

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass

open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G]

theorem original_four_group_coverage_klein
    (z : G)
    (hcover : ∀ V : Subgroup G,
      Nonempty (V ≃* Multiplicative (ZMod 2 × ZMod 2)) →
        ∃ s ∈ V, s ∈ involutionPointClass z) :
    ∀ V : Subgroup G, IsKleinFour V → ∃ s ∈ V, s ∈ involutionPointClass z := by
  intro V hV
  let := hV
  exact hcover V IsKleinFour.nonempty_mulEquiv

theorem original_four_group_coverage_native [Finite G]
    (z : G)
    (hcover : ∀ V : Subgroup G,
      Nonempty (V ≃* Multiplicative (ZMod 2 × ZMod 2)) →
        ∃ s ∈ V, s ∈ involutionPointClass z) :
    ∀ V : Subgroup G, CFSG.Open.IsElemAbelian 2 V → Nat.card V = 4 →
      ∃ s ∈ V, s ∈ involutionPointClass z := by
  intro V hV hcard
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := hV.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun v => Subtype.ext (hV.2 v v.property)) }
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hfour : IsKleinFour V := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  exact original_four_group_coverage_klein z hcover V hfour

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass
