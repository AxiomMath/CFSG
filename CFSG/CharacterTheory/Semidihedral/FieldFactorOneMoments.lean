module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneLocalBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.FourierOddDegreeProduct

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.CompatibleFamily
open CFSG.Wreathed.LinearLocalTwistMoment CFSG.Semidihedral.Principal

variable {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}
  (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}

theorem theta_involution_moment (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (B : basis.index) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      ((multiplicityColumn basis (fS (r n) : G) (modulus n) 0 χ -
          multiplicityColumn basis (fS (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) χ : ℤ) :
          ℂ) *
        ((basis.representation χ).character t ^ 2 / (basis.representation χ).character 1) =
      0 := by
  obtain ⟨hM4, -, -, hhalf⟩ := modulus_eq_four_mul hn
  have h := principal_Fourier_involution_square_sum hn fS basis ideal B
  have hfun : (fun x : Subgroup.zpowers (fS (r n) : G) =>
      1 - cyclicLinearCharacter (fS (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) x) =
      (fun x => cyclicLinearCharacter (fS (r n) : G) (modulus n) 0 x -
        cyclicLinearCharacter (fS (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) x) :=
    funext fun x => by rw [cyclicLinearCharacter_zero]
  rw [hfun] at h
  simp only [characterPairing_linear_difference hn fS basis] at h
  have htr : (fS (r n) : G) ^ (modulus n / 2) = t := by
    rw [ht, show modulus n / 2 = 2 ^ (n - 2) by omega]
  rw [htr] at h
  rw [← h]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [sq]

theorem typeStar_cubic_moment (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2) (θ : C t →* ℂˣ)
    (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (normalizerBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (lambdaLabel : normalizerBasis.index)
    (hlambda : ∀ (x : Subgroup.normalizer ((S : Subgroup G) : Set G)) (q : G)
      (c : Subgroup.centralizer ((S : Subgroup G) : Set G)), q ∈ (S : Subgroup G) →
        (x : G) = q * c → (normalizerBasis.representation lambdaLabel).character x =
          thetaG t θ (c : G))
    (B : basis.index)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _) le_rfl
        normalizerBasis lambdaLabel = centralCharacterResidueHom basis ideal B) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character t ^ 3 / (basis.representation χ).character 1 =
      ∑ χ ∈ principalCoefficientBlock basis ideal,
        (basis.representation χ).character t ^ 3 / (basis.representation χ).character 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : orderOf t = 2 := orderOf_t fS hn ht
  have hu2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have htC : t ∈ C t := by
    rw [C, Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers t : Set G))
  obtain ⟨ψLabel, -, hbr, huniq, hblock⟩ := typeStar_local_block fS hn ht hindex θ hθS hθT
    basis ideal normalizerBasis lambdaLabel hlambda B hB hu2 (Subgroup.mem_zpowers t) htC
    localBasis
  obtain ⟨hbr₀, huniq₀⟩ := principal_local_block fS hn ht hindex basis ideal hu2
    (Subgroup.mem_zpowers t) htC localBasis
  have hSN : (S : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxt : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp (sylow_le_C fS hn ht hx)
    exact (hxt.zpow_right k).symm.eq
  have hS : ∀ z : Subgroup.centralizer (Subgroup.zpowers t : Set G), (z : G) ∈ (S : Subgroup G) →
      family t θ (Subgroup.zpowers t) z = 1 := by
    intro z hz
    rw [family_apply_special fS hn ht θ hθT (special_zpowers (Subgroup.mem_zpowers t) htC) z,
      thetaG_of_mem θ (sylow_le_C fS hn ht hz)]
    exact hθS _ hz
  exact linear_local_twist_preserves_involution_cubic_moment_of_sylow_trivial basis ideal t ht2
    localBasis B ψLabel (family t θ (Subgroup.zpowers t)) S hSN hS hblock hbr₀ huniq₀ hbr huniq

end CFSG.Semidihedral.FieldFactorOne
