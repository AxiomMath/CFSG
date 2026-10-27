module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBWMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

theorem exists_conj_spLeviData_typeBC (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) (hfe : Even f)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hℓ : 3 ≤ finrank K (LinearMap.range (sNil s.val)))
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0) :
    ∃ s₀ a : matrixIsometries (coordinateQuadPlus n K), s = a * s₀ * a⁻¹ ∧
      SpLeviData (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s₀))) := by
  refine ⟨s, 1, by rw [one_mul, inv_one, mul_one], ?_⟩
  have hq4 := four_le_card_of_even hK hfe
  have hB := (regular_coordinateQuadPlus n K (by omega)).1
  have hadj := polar_sNil_left s hss
  have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
  obtain ⟨z, hz⟩ := exists_wallDual (sNil s.val) hadj hNN hB
  rcases quad_wallDual (sNil s.val) hz (polar_sNil_self s) with h0 | h1
  · obtain ⟨w₁, hw₁, hQw₁⟩ := exists_mem_range_quad_eq_one hW
    obtain ⟨zy, rfl⟩ := hw₁
    have heven := even_finrank_range_of_zero (sNil s.val) hadj hNN hz (polar_sNil_self s) h0
      hQw₁ hB
    have hℓ4 : 4 ≤ finrank K (LinearMap.range (sNil s.val)) := by
      obtain ⟨k, hk⟩ := heven
      omega
    exact spLeviData_typeC _ hK hn hq4 s hss hW hℓ4 hz h0 hQw₁
  · exact spLeviData_typeB _ hK hn hq4 s hss hW hℓ hz h1

end CFSG.SeitzReduction.OmegaPilot
