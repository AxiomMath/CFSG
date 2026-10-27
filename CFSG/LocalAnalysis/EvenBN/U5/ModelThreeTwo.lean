module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Open (IsElemAbelian)
open CFSG.ABGLocalTools (IsSylowOf)

theorem exists_mulEquiv_projectiveSL_three_sq {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : LieModel X .PSL 3 2 (2 * f)) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2), Nat.card K' = (2 ^ f) ^ 2 ∧
      Nonempty (X ≃* projectiveSL 3 K') := by
  obtain ⟨K', _, _, hK', he⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP K' 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK'
  exact ⟨K', inferInstance, inferInstance, this, by rw [hK', pow_mul, ← pow_mul, mul_comm,
    pow_mul], he⟩

variable {G : Type} [Group G] {A : Subgroup G} {f : ℕ}

theorem exists_radicals_of_lieModel_sq [Finite G] (hf : 1 ≤ f)
    (hA : LieModel A .PSL 3 2 (2 * f)) {V : Subgroup G} (hV : IsSylowOf 2 V A) :
    ∃ V₁ V₂ : Subgroup G, LinearThree.Radicals V V₁ V₂ ((2 ^ f) ^ 2) := by
  obtain ⟨K', _, _, _, hK', ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_three_sq hf hA
  rw [← hK']
  exact LinearThree.exists_radicals_of_mulEquiv e hV

theorem exists_conj_of_lieModel_sq (hf : 1 ≤ f) (hA : LieModel A .PSL 3 2 (2 * f)) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) :
    ∃ a ∈ A, a * x * a⁻¹ = y := by
  obtain ⟨K', _, _, _, -, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_three_sq hf hA
  exact LinearThree.exists_conj_of_mulEquiv e hx hy hx2 hy2

end CFSG.LocalAnalysis.EvenBN.U5
