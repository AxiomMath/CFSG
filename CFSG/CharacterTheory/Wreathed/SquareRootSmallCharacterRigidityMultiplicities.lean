module

public import CFSG.CharacterTheory.Blocks.RepresentationDecomposition
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram

public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
open scoped BigOperators Classical

variable {G : Type} [Group G]

@[expose] def irreducibleDegree (χ : BlocksIrr G) : ℕ :=
  Classical.choose (blocksIrr_degree_eq_natCast χ)

theorem irreducibleDegree_pos (χ : BlocksIrr G) : 0 < irreducibleDegree χ :=
  (Classical.choose_spec (blocksIrr_degree_eq_natCast χ)).1

theorem irreducibleDegree_cast (χ : BlocksIrr G) :
    (χ : G → ℂ) 1 = (irreducibleDegree χ : ℂ) :=
  (Classical.choose_spec (blocksIrr_degree_eq_natCast χ)).2

theorem natural_expansion_degree (μ : BlocksIrr G →₀ ℕ) :
    (μ.sum fun χ k => (k : ℂ) • (χ : G → ℂ)) 1 =
      ((∑ χ ∈ μ.support, μ χ * irreducibleDegree χ : ℕ) : ℂ) := by
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    irreducibleDegree_cast, Nat.cast_sum, Nat.cast_mul]

theorem multiplicity_degree_le (μ : BlocksIrr G →₀ ℕ) (χ : BlocksIrr G) :
    μ χ * irreducibleDegree χ ≤ ∑ ψ ∈ μ.support, μ ψ * irreducibleDegree ψ := by
  by_cases hχ : χ ∈ μ.support
  · exact Finset.single_le_sum (f := fun ψ => μ ψ * irreducibleDegree ψ)
      (fun _ _ => Nat.zero_le _) hχ
  · rw [Finsupp.notMem_support_iff.mp hχ, zero_mul]
    exact Nat.zero_le _

theorem multiplicity_eq_zero_of_degree_lt (μ : BlocksIrr G →₀ ℕ) (χ : BlocksIrr G)
    {Q : ℕ} (hdegree : (∑ ψ ∈ μ.support, μ ψ * irreducibleDegree ψ) ≤ Q)
    (hχ : Q < irreducibleDegree χ) : μ χ = 0 := by
  have hle := (multiplicity_degree_le μ χ).trans hdegree
  by_contra hzero
  have hpos : 0 < μ χ := Nat.pos_of_ne_zero hzero
  nlinarith

theorem natural_expansion_single_of_degree_bound (μ : BlocksIrr G →₀ ℕ) (χ : BlocksIrr G)
    (hpositive : 0 < μ χ)
    (hdegree : (∑ ψ ∈ μ.support, μ ψ * irreducibleDegree ψ) ≤ irreducibleDegree χ) :
    μ = Finsupp.single χ 1 := by
  have hχ : χ ∈ μ.support := Finsupp.mem_support_iff.mpr hpositive.ne'
  have hle := (multiplicity_degree_le μ χ).trans hdegree
  have hdpos := irreducibleDegree_pos χ
  have hμχ : μ χ = 1 := by nlinarith
  have hrest : ∑ ψ ∈ μ.support.erase χ, μ ψ * irreducibleDegree ψ = 0 := by
    have hsplit := Finset.add_sum_erase μ.support
      (fun ψ => μ ψ * irreducibleDegree ψ) hχ
    rw [hμχ, one_mul] at hsplit
    omega
  ext ψ
  by_cases hψχ : ψ = χ
  · subst ψ
    simp [hμχ]
  · rw [Finsupp.single_eq_of_ne hψχ]
    by_cases hψ : ψ ∈ μ.support
    · have hψerase : ψ ∈ μ.support.erase χ := Finset.mem_erase.mpr ⟨hψχ, hψ⟩
      have hterm := Finset.single_le_sum
        (f := fun η => μ η * irreducibleDegree η) (fun _ _ => Nat.zero_le _) hψerase
      rw [hrest] at hterm
      have hdψ := irreducibleDegree_pos ψ
      nlinarith
    · exact Finsupp.notMem_support_iff.mp hψ

theorem innerProduct_eq_of_agree_on_support [Fintype G]
    (U : Set G) (f g T : G → ℂ) (hT : ∀ x ∉ U, T x = 0)
    (hagree : ∀ x ∈ U, f x = g x) : BlocksInnerProduct f T = BlocksInnerProduct g T := by
  unfold BlocksInnerProduct
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ U
  · rw [hagree x hx]
  · rw [hT x hx]
    simp

@[expose] def signedTest (ε : ℤ) (A B D : BlocksIrr G) : G → ℂ :=
  (1 : G → ℂ) - ε • (A : G → ℂ) - (B : G → ℂ) + ε • (D : G → ℂ)

theorem signedTest_mem_virtual (ε : ℤ) (A B D : BlocksIrr G) :
    signedTest ε A B D ∈ BlocksVChar G := by
  exact (BlocksVChar G).add_mem
    ((BlocksVChar G).sub_mem
      ((BlocksVChar G).sub_mem (AddSubgroup.subset_closure (principal_mem_blocksIrr G))
        ((BlocksVChar G).zsmul_mem (AddSubgroup.subset_closure A.property) ε))
      (AddSubgroup.subset_closure B.property))
    ((BlocksVChar G).zsmul_mem (AddSubgroup.subset_closure D.property) ε)

theorem innerProduct_sub_right [Fintype G] (f g h : G → ℂ) :
    BlocksInnerProduct f (g - h) = BlocksInnerProduct f g - BlocksInnerProduct f h := by
  simp only [BlocksInnerProduct, Pi.sub_apply, map_sub, mul_sub,
    Finset.sum_sub_distrib, mul_sub]

theorem innerProduct_add_right [Fintype G] (f g h : G → ℂ) :
    BlocksInnerProduct f (g + h) = BlocksInnerProduct f g + BlocksInnerProduct f h := by
  simp only [BlocksInnerProduct, Pi.add_apply, map_add, mul_add,
    Finset.sum_add_distrib, mul_add]

theorem innerProduct_zsmul_right [Fintype G] (f g : G → ℂ) (ε : ℤ) :
    BlocksInnerProduct f (ε • g) = (ε : ℂ) * BlocksInnerProduct f g := by
  unfold BlocksInnerProduct
  calc
    (Nat.card G : ℂ)⁻¹ * ∑ x, f x * starRingEnd ℂ ((ε • g) x) =
        (Nat.card G : ℂ)⁻¹ * ∑ x, (ε : ℂ) * (f x * starRingEnd ℂ (g x)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      simp only [Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast]
      ring
    _ = (ε : ℂ) * ((Nat.card G : ℂ)⁻¹ * ∑ x, f x * starRingEnd ℂ (g x)) := by
      rw [← Finset.mul_sum]
      ring

theorem innerProduct_signedTest [Fintype G] (f : G → ℂ) (ε : ℤ) (A B D : BlocksIrr G) :
    BlocksInnerProduct f (signedTest ε A B D) =
      BlocksInnerProduct f 1 - (ε : ℂ) * BlocksInnerProduct f (A : G → ℂ) -
        BlocksInnerProduct f (B : G → ℂ) + (ε : ℂ) * BlocksInnerProduct f (D : G → ℂ) := by
  simp only [signedTest, innerProduct_add_right, innerProduct_sub_right,
    innerProduct_zsmul_right]

theorem character_eq_of_agree_on_signed_support [Fintype G]
    (A B D : BlocksIrr G) (ε : ℤ) (U : Set G)
    (hB : (B : G → ℂ) ≠ 1)
    (hA : irreducibleDegree B < irreducibleDegree A)
    (hD : irreducibleDegree B < irreducibleDegree D)
    (hsupport : ∀ x ∉ U, signedTest ε A B D x = 0)
    (θ : FiniteComplexRepresentation.{0, 0} G)
    (hdegree : Module.finrank ℂ θ.vector ≤ irreducibleDegree B)
    (hagree : ∀ x ∈ U, θ.character x = (B : G → ℂ) x) :
    θ.character = (B : G → ℂ) := by
  obtain ⟨μ, hμ, _⟩ := (complex_representation_character_decomposition θ.representation).2.1
  change θ.character = μ.sum (fun χ k => (k : ℂ) • (χ : G → ℂ)) at hμ
  have honeθ : θ.character 1 = (Module.finrank ℂ θ.vector : ℂ) :=
    Representation.char_one θ.representation
  have hdegreeμ : (∑ χ ∈ μ.support, μ χ * irreducibleDegree χ) =
      Module.finrank ℂ θ.vector := by
    have h := congrFun hμ 1
    rw [honeθ, natural_expansion_degree] at h
    exact_mod_cast h.symm
  have hbound : (∑ χ ∈ μ.support, μ χ * irreducibleDegree χ) ≤ irreducibleDegree B := by
    rwa [hdegreeμ]
  have hμA := multiplicity_eq_zero_of_degree_lt μ A hbound hA
  have hμD := multiplicity_eq_zero_of_degree_lt μ D hbound hD
  let P : BlocksIrr G := ⟨1, principal_mem_blocksIrr G⟩
  have hBP : B ≠ P := fun h => hB (congrArg Subtype.val h)
  have hBA : B ≠ A := by
    intro h
    rw [h] at hA
    exact (lt_irrefl _ hA)
  have hBD : B ≠ D := by
    intro h
    rw [h] at hD
    exact (lt_irrefl _ hD)
  have hpairB : BlocksInnerProduct (B : G → ℂ) (signedTest ε A B D) = -1 := by
    rw [innerProduct_signedTest]
    change BlocksInnerProduct (B : G → ℂ) (P : G → ℂ) -
      (ε : ℂ) * BlocksInnerProduct (B : G → ℂ) (A : G → ℂ) -
      BlocksInnerProduct (B : G → ℂ) (B : G → ℂ) +
      (ε : ℂ) * BlocksInnerProduct (B : G → ℂ) (D : G → ℂ) = -1
    simp only [blocksInnerProduct_irreducible, hBP, hBA, hBD, ite_false, ite_true]
    ring
  have hpairθ := innerProduct_eq_of_agree_on_support U θ.character (B : G → ℂ)
    (signedTest ε A B D) hsupport hagree
  rw [hpairB, innerProduct_signedTest] at hpairθ
  have hcoeff (χ : BlocksIrr G) : BlocksInnerProduct θ.character (χ : G → ℂ) = (μ χ : ℂ) := by
    rw [hμ]
    exact natural_expansion_coefficient μ χ
  change BlocksInnerProduct θ.character (P : G → ℂ) -
    (ε : ℂ) * BlocksInnerProduct θ.character (A : G → ℂ) -
    BlocksInnerProduct θ.character (B : G → ℂ) +
    (ε : ℂ) * BlocksInnerProduct θ.character (D : G → ℂ) = -1 at hpairθ
  simp only [hcoeff, hμA, hμD, Nat.cast_zero, mul_zero, sub_zero, add_zero] at hpairθ
  have hcoeffInt : (μ P : ℤ) - (μ B : ℤ) = -1 := by exact_mod_cast hpairθ
  have hpositive : 0 < μ B := by omega
  have hsingle := natural_expansion_single_of_degree_bound μ B hpositive hbound
  rw [hsingle] at hμ
  simpa using hμ

theorem square_root_degree_bounds {q Q : ℕ} {ε : ℤ}
    (hq : 5 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (hQ : (Q : ℤ) = (q : ℤ) ^ 2 + ε * q + 1) :
    1 < Q ∧ Q < q ^ 3 ∧ Q < q * Q := by
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hQpos : (1 : ℤ) < Q := by
    rcases hε with rfl | rfl <;> nlinarith
  have hQcubic : (Q : ℤ) < (q : ℤ) ^ 3 := by
    have hq2 : (25 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
    have hq3 : (5 : ℤ) * (q : ℤ) ^ 2 ≤ (q : ℤ) ^ 3 := by nlinarith
    rcases hε with rfl | rfl <;> nlinarith
  refine ⟨by exact_mod_cast hQpos, by exact_mod_cast hQcubic, ?_⟩
  have hmul : (Q : ℤ) < (q : ℤ) * Q := by nlinarith
  exact_mod_cast hmul

theorem character_eq_of_square_root_degrees_and_support [Fintype G]
    (A B D : BlocksIrr G) {q Q : ℕ} (ε : ℤ)
    (hq : 5 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (hQ : (Q : ℤ) = (q : ℤ) ^ 2 + ε * q + 1)
    (hA : (A : G → ℂ) 1 = (q ^ 3 : ℕ))
    (hB : (B : G → ℂ) 1 = (Q : ℂ))
    (hD : (D : G → ℂ) 1 = (q * Q : ℕ))
    (U : Set G) (hsupport : ∀ x ∉ U, signedTest ε A B D x = 0)
    (θ : FiniteComplexRepresentation.{0, 0} G)
    (hdegree : Module.finrank ℂ θ.vector ≤ Q)
    (hagree : ∀ x ∈ U, θ.character x = (B : G → ℂ) x) :
    θ.character = (B : G → ℂ) ∧ Module.finrank ℂ θ.vector = Q := by
  have hdegA : irreducibleDegree A = q ^ 3 := by
    exact_mod_cast (irreducibleDegree_cast A).symm.trans hA
  have hdegB : irreducibleDegree B = Q := by
    exact_mod_cast (irreducibleDegree_cast B).symm.trans hB
  have hdegD : irreducibleDegree D = q * Q := by
    exact_mod_cast (irreducibleDegree_cast D).symm.trans hD
  obtain ⟨hQone, hQA, hQD⟩ := square_root_degree_bounds hq hε hQ
  have hBnonprincipal : (B : G → ℂ) ≠ 1 := by
    intro h
    have hvalue := congrFun h 1
    rw [hB, Pi.one_apply] at hvalue
    have hQ1 : Q = 1 := by exact_mod_cast hvalue
    omega
  have heq := character_eq_of_agree_on_signed_support A B D ε U hBnonprincipal
    (by rwa [hdegB, hdegA]) (by rwa [hdegB, hdegD]) hsupport θ
    (by rwa [hdegB]) hagree
  refine ⟨heq, ?_⟩
  have hvalue := congrFun heq 1
  change θ.representation.character 1 = (B : G → ℂ) 1 at hvalue
  rw [Representation.char_one, hB] at hvalue
  exact_mod_cast hvalue

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
