module

public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem canonicalRep_conj_charTwo
    {τ : Tag} {K : Type} [Field K] [CharP K 2] (w : WeylGroup τ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (x : K) :
    canonicalRep (coxeterSystem τ) K w * pinnedX τ K α x * (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      pinnedX τ K (w • α) x := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hα
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : (ε - 1) ^ 2 = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  rw [h, hε1, one_mul]

end CFSG.QuasithinUnique.K1
