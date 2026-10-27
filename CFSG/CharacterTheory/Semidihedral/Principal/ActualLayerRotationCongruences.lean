module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerDegreeProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerRotationCongruencesSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Wreathed CFSG.Open

theorem actual_nonsimple_layer_odd_character_rotation_congruences {G : Type} [Group G]
    [Fintype G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : Gamma t →* coordinateE F),
      Nat.card F = p ^ f ∧ Function.Injective ρ ∧
      (CFSG.generalizedFitting (Gamma t)).map ρ = specialLayer F ∧ linearLayer F ≤ ρ.range ∧
      (let φ : C t → ℂ := fun c =>
        (Nat.card {x : Omega F // ((ρ (kappa t c) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let e : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      φ 1 = Nat.card F ∧ (∃ y : C t, Odd (orderOf y) ∧ φ y ≠ Nat.card F) ∧
      (∃ (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
        ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
          (Nat.card F) e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
        ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄) ∧
      ∀ (φ' : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
        ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
            (Nat.card F) e (2 ^ (n - 3)) φ' δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
          ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ →
        (∃ (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G)),
          (e' (r n) : G) ^ (modulus n / 2) = t) ∧
        (∀ (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G)),
          (e' (r n) : G) ^ (modulus n / 2) = t →
          ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] → ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
            (basis.representation χ₁).character ((e' (r n) : G) ^ v) = δ₁ ∧
            (basis.representation χ₂).character ((e' (r n) : G) ^ v) = -δ₂ * (-1 : ℂ) ^ v ∧
            (basis.representation χ₃).character ((e' (r n) : G) ^ v) = -δ₃ * (-1 : ℂ) ^ v) ∧
        (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) ≡
          δ₁ * (2 - e * Nat.card F) [ZMOD 8] ∧
        (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) ≡
          -δ₂ * e * Nat.card F [ZMOD 8] ∧
        (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) ≡ -δ₃ [ZMOD 8]) := by
  obtain ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hlin, hrest⟩ :=
    actual_nonsimple_layer_principal_degree_product n hn S0 f0 hG t ht hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  refine ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hlin, ?_⟩
  intro φ e
  obtain ⟨hφ1, hφnc, hfam⟩ := hrest
  refine ⟨hφ1, hφnc, hfam, ?_⟩
  intro φ' δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ⟨hfam', hdeg'⟩
  obtain ⟨hq3, hqodd⟩ := three_le_and_odd_of_prime_pow hp hpodd hf
  rw [← hcard] at hq3 hqodd
  have he1 : Nat.card F % 4 = 1 → e = 1 := fun h => by simp only [e, h, ite_true]
  have he3 : Nat.card F % 4 = 3 → e = -1 := fun h => by
    simp only [e, show Nat.card F % 4 ≠ 1 by omega, ite_false]
  have hpres : ∃ (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G)),
      (e' (r n) : G) ^ (modulus n / 2) = t := by
    obtain ⟨-, St, ft, -, hft⟩ :=
      InvolutionFusion.involution_centered_sylow_existence n hn S0 f0 hG t ht
    refine ⟨St, ft, ?_⟩
    have hM : modulus n / 2 = 2 ^ (n - 2) := by
      rw [modulus, show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos]
    rw [hM, ← Subgroup.coe_pow]
    exact hft
  obtain ⟨St, ft, hft⟩ := hpres
  have hcore := fun (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G))
      (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) =>
    actual_principal_rotation_values_and_congruences hG hn ht hnonab basis ideal principal
      hprincipal localBasis localPrincipal (Nat.card F) hq3 hqodd e he1 he3 φ' δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam' hdeg' e' hcent
  exact ⟨⟨St, ft, hft⟩, fun S e' hcent => (hcore S e' hcent).1, (hcore St ft hft).2⟩

theorem actual_simple_layer_odd_character_rotation_congruences {G : Type} [Group G] [Fintype G]
    [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : Gamma t →* coordinateE F),
      Nat.card F = p ^ f ∧ Function.Injective ρ ∧
      (CFSG.generalizedFitting (Gamma t)).map ρ = specialLayer F ∧ linearLayer F ≤ ρ.range ∧
      (let φ : C t → ℂ := fun c =>
        (Nat.card {x : Omega F // ((ρ (kappa t c) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let e : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      φ 1 = Nat.card F ∧ (∃ y : C t, Odd (orderOf y) ∧ φ y ≠ Nat.card F) ∧
      (∃ (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
        ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
          (Nat.card F) e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
        ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄) ∧
      ∀ (φ' : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
        ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
            (Nat.card F) e (2 ^ (n - 3)) φ' δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
          ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ →
        (∃ (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G)),
          (e' (r n) : G) ^ (modulus n / 2) = t) ∧
        (∀ (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G)),
          (e' (r n) : G) ^ (modulus n / 2) = t →
          ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] → ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
            (basis.representation χ₁).character ((e' (r n) : G) ^ v) = δ₁ ∧
            (basis.representation χ₂).character ((e' (r n) : G) ^ v) = -δ₂ * (-1 : ℂ) ^ v ∧
            (basis.representation χ₃).character ((e' (r n) : G) ^ v) = -δ₃ * (-1 : ℂ) ^ v) ∧
        (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) ≡
          δ₁ * (2 - e * Nat.card F) [ZMOD 8] ∧
        (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) ≡
          -δ₂ * e * Nat.card F [ZMOD 8] ∧
        (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) ≡ -δ₃ [ZMOD 8]) :=
  actual_nonsimple_layer_odd_character_rotation_congruences n hn S0 f0
    (index_ne_two_of_isSimpleGroup hGnonab) t ht hnonab hcentral hnc p f hp hpodd hf hmodel ideal
    basis principal hprincipal localBasis localPrincipal hlocalPrincipal

end CFSG.Semidihedral.Principal
