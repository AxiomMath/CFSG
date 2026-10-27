module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open CFSG

universe u v

variable {A : Type u} [Group A]
variable {I : Type v} [Group I] [MulDistribMulAction A I]

theorem odd_square_mem_implies_mem [Finite I] (hodd : Odd (Nat.card I))
    (K : Subgroup I) (x : I) (hx : x ^ 2 ∈ K) : x ∈ K := by
  have hord : Odd (orderOf x) := hodd.of_dvd_nat (orderOf_dvd_natCard x)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := x) hord.coprime_two_left
  rw [← hm]
  exact K.pow_mem hx m

theorem odd_inverted_element_mem_commutator [Finite I] (hodd : Odd (Nat.card I))
    (b : A) (J : Subgroup I) (x : I) (hx : x ∈ J) (hanti : b • x = x⁻¹) :
    x ∈ actorCommutatorSubgroup b J := by
  apply odd_square_mem_implies_mem hodd
  have hgen := actorCommutatorSubgroup_generator_mem b hx
  rw [hanti] at hgen
  have hsq : x ^ 2 = (x⁻¹ * x⁻¹)⁻¹ := by simp [pow_two]
  rw [hsq]
  exact (actorCommutatorSubgroup b J).inv_mem hgen

theorem odd_involution_fixed_inverted_decomposition [Finite I]
    (hodd : Odd (Nat.card I)) (b : A) (hb : b * b = 1)
    (J : Subgroup I) [IsInvariant A I J] (x : I) (hx : x ∈ J) :
    ∃ c ∈ J, ∃ r ∈ J, b • c = c ∧ b • r = r⁻¹ ∧ x = c * r := by
  let X : J := ⟨x, hx⟩
  have hJodd : Odd (Nat.card J) := hodd.of_dvd_nat J.card_subgroup_dvd_card
  let φ : J → J := fun y => b • y
  have hφφ (y : J) : φ (φ y) = y := by
    change b • (b • y) = y
    rw [← mul_smul, hb, one_smul]
  let d : J := (φ X)⁻¹ * X
  obtain ⟨R, hR⟩ := BenderSuzuki.PFchapter1section1.sq_surjective_of_odd_card hJodd d
  change R ^ 2 = d at hR
  have hsquare_inj : Function.Injective (fun y : J => y ^ 2) :=
    Finite.injective_iff_surjective.2
      (BenderSuzuki.PFchapter1section1.sq_surjective_of_odd_card hJodd)
  have hRanti : φ R = R⁻¹ := by
    apply hsquare_inj
    calc
      (φ R) ^ 2 = φ (R ^ 2) := by simp [φ, pow_two, smul_mul']
      _ = φ d := by rw [hR]
      _ = d⁻¹ := by simp [φ, d, smul_mul', smul_inv', hφφ]
      _ = (R⁻¹) ^ 2 := by rw [← hR]; simp [pow_two]
  let C : J := X * R⁻¹
  have hCfixed : φ C = C := by
    have hX : X = φ X * R ^ 2 := by rw [hR]; simp [d]
    calc
      φ C = φ X * (φ R)⁻¹ := by simp only [C, φ, smul_mul', smul_inv']
      _ = φ X * R := by rw [hRanti]; simp
      _ = φ X * (R ^ 2 * R⁻¹) := by simp [pow_two, mul_assoc]
      _ = X * R⁻¹ := by rw [← mul_assoc, ← hX]
  refine ⟨C, C.property, R, R.property, congrArg Subtype.val hCfixed,
    congrArg Subtype.val hRanti, ?_⟩
  change x = (x * (R : I)⁻¹) * R
  simp [mul_assoc]

theorem odd_involution_fixed_commutator_factorization [Finite I]
    (hodd : Odd (Nat.card I)) (b : A) (hb : b * b = 1)
    (J : Subgroup I) [IsInvariant A I J] (x : I) (hx : x ∈ J) :
    ∃ c ∈ J, ∃ r ∈ actorCommutatorSubgroup b J, b • c = c ∧ x = c * r := by
  obtain ⟨c, hc, r, hr, hcf, hra, hprod⟩ :=
    odd_involution_fixed_inverted_decomposition hodd b hb J x hx
  exact ⟨c, hc, r, odd_inverted_element_mem_commutator hodd b J r hr hra, hcf, hprod⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
