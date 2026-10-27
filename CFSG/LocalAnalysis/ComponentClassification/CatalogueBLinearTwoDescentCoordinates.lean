module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentNative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateSemilinear

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoDescent

noncomputable section

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u

theorem coordinate_semilinear_square_data (K : Type u) [Field K] [Finite K]
    (d : coordinateD K) (sigma : K ≃+* K)
    (ha : ((d : Equiv.Perm (Omega K)) * fieldExtension K sigma) ^ 2 = 1) :
    sigma ^ 2 = 1 ∧
      (pglEquivCoordinateD K).symm d *
        pgl2RingEquiv sigma ((pglEquivCoordinateD K).symm d) = 1 := by
  let g : PGL2 K := (pglEquivCoordinateD K).symm d
  let a : PGammaL2 K := SemidirectProduct.inl g * SemidirectProduct.inr sigma
  have hg : coordinatePGLAction K g = (d : Equiv.Perm (Omega K)) := by
    exact congrArg Subtype.val ((pglEquivCoordinateD K).apply_symm_apply d)
  have hact : coordinateSemilinearAction K a =
      (d : Equiv.Perm (Omega K)) * fieldExtension K sigma := by
    dsimp [a]
    rw [map_mul, coordinateSemilinearAction_inl, coordinateSemilinearAction_inr, hg]
  have hasq : a ^ 2 = 1 := by
    apply coordinateSemilinearAction_injective K
    rw [map_pow, hact, ha, map_one]
  have hsig : sigma ^ 2 = 1 := by
    have h := congrArg SemidirectProduct.right hasq
    simpa [a, pow_two] using h
  refine ⟨hsig, ?_⟩
  have h := congrArg SemidirectProduct.left hasq
  simpa [a, pow_two, pgl2FieldAut_apply] using h

theorem coordinate_semilinear_involution_conjugacy (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (d : coordinateD K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (ha : ((d : Equiv.Perm (Omega K)) * fieldExtension K sigma) ^ 2 = 1) :
    ∃ h : coordinateD K,
      (d : Equiv.Perm (Omega K)) * fieldExtension K sigma =
        (h : Equiv.Perm (Omega K)) * fieldExtension K sigma *
          (h : Equiv.Perm (Omega K))⁻¹ := by
  let g : PGL2 K := (pglEquivCoordinateD K).symm d
  let a : PGammaL2 K := SemidirectProduct.inl g * SemidirectProduct.inr sigma
  have hg : coordinatePGLAction K g = (d : Equiv.Perm (Omega K)) := by
    exact congrArg Subtype.val ((pglEquivCoordinateD K).apply_symm_apply d)
  have hact : coordinateSemilinearAction K a =
      (d : Equiv.Perm (Omega K)) * fieldExtension K sigma := by
    dsimp [a]
    rw [map_mul, coordinateSemilinearAction_inl, coordinateSemilinearAction_inr, hg]
  have hasq : a ^ 2 = 1 := by
    apply coordinateSemilinearAction_injective K
    rw [map_pow, hact, ha, map_one]
  have hafield : a.right ≠ 1 := by simpa [a] using hne
  have hane : a ≠ 1 := by
    intro h
    exact hafield (congrArg SemidirectProduct.right h)
  have haord : orderOf a = 2 := orderOf_eq_prime hasq hane
  obtain ⟨h, hh⟩ := native_semilinear_involution_conjugacy hK a haord hafield
  refine ⟨pglEquivCoordinateD K h, ?_⟩
  have hcoe : ((pglEquivCoordinateD K h : coordinateD K) : Equiv.Perm (Omega K)) =
      coordinatePGLAction K h := rfl
  rw [hcoe]
  have h := congrArg (coordinateSemilinearAction K) hh
  simpa [map_mul, map_inv, coordinateSemilinearAction_inl,
    coordinateSemilinearAction_inr, hact, a] using h

theorem quadratic_semilinear_involution_conjugacy (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f)
    (d : coordinateD K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (ha : ((d : Equiv.Perm (Omega K)) * fieldExtension K sigma) ^ 2 = 1) :
    Even f ∧ (∀ x : K, sigma x = x ^ (p ^ (f / 2))) ∧
      Nat.card (fixedSubfield K sigma) = p ^ (f / 2) ∧
      ∃ h : coordinateD K,
        (d : Equiv.Perm (Omega K)) * fieldExtension K sigma =
          (h : Equiv.Perm (Omega K)) * fieldExtension K sigma *
            (h : Equiv.Perm (Omega K))⁻¹ := by
  have hK : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hodd, hf, hcard⟩
  have hsigma := (coordinate_semilinear_square_data K d sigma ha).1
  obtain ⟨heven, hformula, hfixed⟩ := quadraticField_parameters K p f hp hcard sigma hsigma hne
  exact ⟨heven, hformula, hfixed,
    coordinate_semilinear_involution_conjugacy K hK d sigma hne ha⟩

theorem native_quadratic_semilinear_involution_conjugacy
    (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f)
    (a : PGammaL2 K) (ha : orderOf a = 2) (hfield : a.right ≠ 1) :
    Even f ∧ (∀ x : K, a.right x = x ^ (p ^ (f / 2))) ∧
      Nat.card (fixedSubfield K a.right) = p ^ (f / 2) ∧
      ∃ h : PGL2 K,
        a = SemidirectProduct.inl h * SemidirectProduct.inr a.right *
          (SemidirectProduct.inl h)⁻¹ := by
  have hK : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hodd, hf, hcard⟩
  have hasq : a ^ 2 = 1 := by simpa [ha] using pow_orderOf_eq_one a
  have hsigma : a.right ^ 2 = 1 := by
    have h := congrArg SemidirectProduct.right hasq
    simpa [pow_two] using h
  obtain ⟨heven, hformula, hfixed⟩ :=
    quadraticField_parameters K p f hp hcard a.right hsigma hfield
  exact ⟨heven, hformula, hfixed,
    native_semilinear_involution_conjugacy hK a ha hfield⟩

theorem quadratic_semilinear_involution_conjugacy_in_E
    (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f)
    (a : coordinateE K) (d : coordinateD K) (sigma : K ≃+* K)
    (hne : sigma ≠ 1)
    (ha : (a : Equiv.Perm (Omega K)) =
      (d : Equiv.Perm (Omega K)) * fieldExtension K sigma)
    (hinvolution : a ^ 2 = 1) :
    Even f ∧ (∀ x : K, sigma x = x ^ (p ^ (f / 2))) ∧
      Nat.card (fixedSubfield K sigma) = p ^ (f / 2) ∧
      ∃ h : coordinateD K,
        (a : Equiv.Perm (Omega K)) =
          (h : Equiv.Perm (Omega K)) * fieldExtension K sigma *
            (h : Equiv.Perm (Omega K))⁻¹ := by
  have hsquare : ((d : Equiv.Perm (Omega K)) * fieldExtension K sigma) ^ 2 = 1 := by
    rw [← ha]
    exact congrArg Subtype.val hinvolution
  obtain ⟨heven, hformula, hfixed, h, hh⟩ :=
    quadratic_semilinear_involution_conjugacy K p f hp hodd hf hcard d sigma hne hsquare
  exact ⟨heven, hformula, hfixed, h, ha.trans hh⟩

end

end CFSG.ComponentClassification.CatalogueBLinearTwoDescent
