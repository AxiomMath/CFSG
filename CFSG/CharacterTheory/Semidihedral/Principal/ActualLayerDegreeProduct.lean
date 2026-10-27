module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualSimpleLayerExhaustion
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerDegreeProductSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Wreathed CFSG.Open

theorem index_ne_two_of_isSimpleGroup {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (U : Subgroup G) : U.index ≠ 2 := by
  intro hindex
  have hU : U.Normal := Subgroup.normal_of_index_eq_two hindex
  rcases hU.eq_bot_or_eq_top with rfl | rfl
  · rw [Subgroup.index_bot] at hindex
    have : Fact (Nat.Prime (Nat.card G)) := ⟨hindex ▸ Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card rfl
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [Subgroup.index_top] at hindex
    omega

theorem three_le_and_odd_of_prime_pow {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) :
    3 ≤ p ^ f ∧ Odd (p ^ f) := by
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · subst h
      exact absurd hpodd (by decide)
    · have := hp.two_le
      obtain ⟨k, hk⟩ := h
      omega
  refine ⟨?_, hpodd.pow⟩
  calc 3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf

theorem actual_nonsimple_layer_principal_degree_product {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
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
      ∃ (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
        ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
          (Nat.card F) e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
        ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄) := by
  obtain ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hlin, hrest⟩ :=
    actual_simple_layer_principal_block_exhaustion_and_values n hn S0 f0 hG t ht hnonab
      hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal
  refine ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hlin, ?_⟩
  intro φ e
  obtain ⟨hφ1, hφnc, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam⟩ := hrest
  refine ⟨hφ1, hφnc, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, ?_⟩
  obtain ⟨-, St, ft, -, hft⟩ :=
    InvolutionFusion.involution_centered_sylow_existence n hn S0 f0 hG t ht
  have hcent : (ft (r n) : G) ^ (modulus n / 2) = t := by
    have hM : modulus n / 2 = 2 ^ (n - 2) := by
      rw [modulus, show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos]
    rw [hM, ← Subgroup.coe_pow]
    exact hft
  obtain ⟨hq3, hqodd⟩ := three_le_and_odd_of_prime_pow hp hpodd hf
  rw [← hcard] at hq3 hqodd
  have he : e = 1 ∨ e = -1 := by
    simp only [e]
    split_ifs <;> simp
  exact actual_principal_degree_relations_of_family hG hn ft hcent basis ideal principal
    hprincipal localBasis localPrincipal (Nat.card F) hq3 hqodd e he (2 ^ (n - 3)) φ hφ1 hφnc
    δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam

theorem actual_simple_layer_principal_degree_product {G : Type} [Group G] [Fintype G]
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
      ∃ (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
        ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
          (Nat.card F) e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
        ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄) :=
  actual_nonsimple_layer_principal_degree_product n hn S0 f0
    (index_ne_two_of_isSimpleGroup hGnonab) t ht hnonab hcentral hnc p f hp hpodd hf hmodel ideal
    basis principal hprincipal localBasis localPrincipal hlocalPrincipal

end CFSG.Semidihedral.Principal
