module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoInvolutionField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoInvolutionEquiv

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoInvolution

noncomputable section

open CFSG.GorensteinWalter CatalogueSchreierLinearTwo

universe u

theorem fieldExtension_one (K : Type u) [Field K] : fieldExtension K 1 = 1 := by
  ext x
  cases x with
  | none => rfl
  | some x => rfl

theorem linear_involution_fixedGroup_solvable (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card K = p ^ f)
    (a : Equiv.Perm (Omega K)) (haD : a ∈ coordinateD K) (ha : orderOf a = 2) :
    Group.IsSolvable (fixedGroup K a) := by
  let d : coordinateD K := ⟨a, haD⟩
  have hne : d ≠ 1 := by
    intro h
    have hval : a = 1 := congrArg Subtype.val h
    rw [hval, orderOf_one] at ha
    omega
  have hsquare : d ^ 2 = 1 := by
    apply Subtype.ext
    change a ^ 2 = 1
    simpa only [ha] using pow_orderOf_eq_one a
  exact (CatalogueBLinearTwo.coordinate_involution_centralizer_structure K
    (two_ne_zero_of_card K p f hp hodd hcard) d hne hsquare).2.2.2

theorem nonlinear_involution_fixedGroup_structure (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f)
    (a : coordinateE K) (ha : orderOf (a : Equiv.Perm (Omega K)) = 2)
    (hnonlinear : (a : Equiv.Perm (Omega K)) ∉ coordinateD K) :
    ∃ sigma : K ≃+* K, orderOf sigma = 2 ∧ Even f ∧
      (∀ x : K, sigma x = x ^ (p ^ (f / 2))) ∧
      Nat.card (CatalogueBLinearTwoFixed.fixedField K sigma) = p ^ (f / 2) ∧
      Nonempty (coordinateD (CatalogueBLinearTwoFixed.fixedField K sigma) ≃*
        fixedGroup K (a : Equiv.Perm (Omega K))) := by
  obtain ⟨d, sigma, hdecomp⟩ := coordinateNormalizer_decomposition K a
    (coordinateE_le_normalizer_G K a.property)
  have hsigmaNe : sigma ≠ 1 := by
    intro h
    apply hnonlinear
    rw [hdecomp, h, fieldExtension_one, mul_one]
    exact d.property
  have haSquare : a ^ 2 = 1 := by
    apply Subtype.ext
    change (a : Equiv.Perm (Omega K)) ^ 2 = 1
    simpa only [ha] using pow_orderOf_eq_one (a : Equiv.Perm (Omega K))
  have hdecompSquare : ((d : Equiv.Perm (Omega K)) * fieldExtension K sigma) ^ 2 = 1 := by
    rw [← hdecomp]
    exact congrArg Subtype.val haSquare
  have hsigmaSquare :=
    (CatalogueBLinearTwoDescent.coordinate_semilinear_square_data K d sigma hdecompSquare).1
  have hsigma : orderOf sigma = 2 := orderOf_eq_prime hsigmaSquare hsigmaNe
  obtain ⟨heven, hformula, hfixed, h, hconj⟩ :=
    CatalogueBLinearTwoDescent.quadratic_semilinear_involution_conjugacy_in_E
      K p f hp hodd hf hcard a d sigma hsigmaNe hdecomp haSquare
  have hnormalize : (h : Equiv.Perm (Omega K)) ∈
      Subgroup.normalizer (coordinateG K : Set (Equiv.Perm (Omega K))) :=
    coordinateE_le_normalizer_G K (coordinateD_le_E K h.property)
  let e := (subfieldFixedEquiv K (ringChar_ne_two_of_card K p f hp hodd hcard)
      sigma hsigma).trans
    (normalizerFixedEquiv (coordinateG K) h hnormalize (fieldExtension K sigma))
  let ea := e.trans (MulEquiv.subgroupCongr (congrArg (fixedGroup K) hconj.symm))
  exact ⟨sigma, hsigma, heven, hformula, hfixed, ⟨ea⟩⟩

theorem involution_fixedGroup_alternative (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f)
    (a : coordinateE K) (ha : orderOf (a : Equiv.Perm (Omega K)) = 2) :
    Group.IsSolvable (fixedGroup K (a : Equiv.Perm (Omega K))) ∨
      ∃ sigma : K ≃+* K, orderOf sigma = 2 ∧ Even f ∧
        (∀ x : K, sigma x = x ^ (p ^ (f / 2))) ∧
        Nat.card (CatalogueBLinearTwoFixed.fixedField K sigma) = p ^ (f / 2) ∧
        Nonempty (coordinateD (CatalogueBLinearTwoFixed.fixedField K sigma) ≃*
          fixedGroup K (a : Equiv.Perm (Omega K))) := by
  classical
  by_cases hlinear : (a : Equiv.Perm (Omega K)) ∈ coordinateD K
  · exact Or.inl (linear_involution_fixedGroup_solvable K p f hp hodd hcard a hlinear ha)
  · exact Or.inr
      (nonlinear_involution_fixedGroup_structure K p f hp hodd hf hcard a ha hlinear)

end

end CFSG.ComponentClassification.CatalogueBLinearTwoInvolution
