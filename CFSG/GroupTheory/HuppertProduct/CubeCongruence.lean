module

public import CFSG.GroupTheory.HuppertProduct.Mho
import CFSG.GroupTheory.HuppertProduct.CubeIdentity
import CFSG.GroupTheory.HuppertProduct.Quotient

public section

open scoped commutatorElement

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

theorem cube_mul_mem {H : Subgroup G} (hcomm : ⁅H, H⁆ ≤ mho H 3)
    (hpow : ⁅mho H 3, H⁆ ≤ mho (mho H 3) 3) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    (x ^ 3 * y ^ 3)⁻¹ * (x * y) ^ 3 ∈ mho (mho H 3) 3 := by
  obtain ⟨Γ, _, π, -, hπ⟩ := exists_quotient (le_normalizer_mho_mho H 3 3)
  have hdM : ⁅y, x⁆ ∈ mho H 3 := hcomm (Subgroup.commutator_mem_commutator hy hx)
  have hdH : ⁅y, x⁆ ∈ H := mho_le H 3 hdM
  let x' : H := ⟨x, hx⟩
  let y' : H := ⟨y, hy⟩
  let c' : H := ⟨⁅y, x⁆, hdH⟩
  have hc' : c' = ⁅y', x'⁆ := rfl
  have hc3 : π c' ^ 3 = 1 := by
    rw [← map_pow]
    exact (hπ _).2 (by simpa [c'] using pow_mem_mho (n := 3) hdM)
  have hcen : ∀ h : H, ⁅π c', π h⁆ = 1 := by
    intro h
    rw [← map_commutatorElement]
    refine (hπ _).2 ?_
    have : ⁅⁅y, x⁆, (h : G)⁆ ∈ ⁅mho H 3, H⁆ := Subgroup.commutator_mem_commutator hdM h.2
    simpa [c', commutatorElement_def] using hpow this
  have key := mul_pow_three_of_commute (x := π x') (y := π y')
    (commutatorElement_eq_one_iff_commute.1 (by simpa [← map_commutatorElement, hc'] using hcen x'))
    (commutatorElement_eq_one_iff_commute.1 (by simpa [← map_commutatorElement, hc'] using hcen y'))
  rw [← map_commutatorElement, ← hc', hc3, one_mul] at key
  have : π ((x' ^ 3 * y' ^ 3)⁻¹ * (x' * y') ^ 3) = 1 := by
    simp only [map_mul, map_inv, map_pow]
    rw [key]
    simp
  simpa [x', y'] using (hπ _).1 this

end CFSG.GroupTheory.HuppertProduct
