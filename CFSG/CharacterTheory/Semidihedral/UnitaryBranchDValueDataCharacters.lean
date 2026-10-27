module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerCharacteristicValuation
public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOrdersSupport
public import CFSG.CharacterTheory.BlockBasics.LocalRing

public section

open scoped Classical

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers

theorem unitary_principal_characters
    (G : Type) [Group G] [Fintype G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq1 : p ^ f % 4 = 1)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hval : 3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})) : ℤ) ≤
      padicValNat p (Nat.card G))
    (basis : FiniteIrreducibleCharacterBasis G) :
    (∃ χ₁ ψ : basis.index,
      Module.finrank ℂ (basis.representation χ₁).vector = (p ^ f) ^ 3 ∧
      Module.finrank ℂ (basis.representation ψ).vector = (p ^ f) ^ 3 + 1 ∧
      ((basis.representation ψ).character t = ((p ^ f : ℕ) : ℂ) + 1 ∨
        (basis.representation ψ).character t = -(((p ^ f : ℕ) : ℂ) + 1)) ∧
      ∀ g : G, Odd (orderOf g) →
        (basis.representation ψ).character g = (basis.representation χ₁).character g + 1) ∧
    ∀ χ : basis.index, (∀ g, starRingEnd ℂ ((basis.representation χ).character g) =
        (basis.representation χ).character g) →
      Odd (Module.finrank ℂ (basis.representation χ).vector) →
      Module.finrank ℂ (basis.representation χ).vector = 1 ∨
      Module.finrank ℂ (basis.representation χ).vector = (p ^ f) ^ 3 ∨
      Module.finrank ℂ (basis.representation χ).vector = (p ^ f) ^ 2 - p ^ f + 1 ∨
      Module.finrank ℂ (basis.representation χ).vector = p ^ f * ((p ^ f) ^ 2 - p ^ f + 1) := by
  classical
  obtain ⟨-, ht2, hcentR, -, -, -⟩ := Principal.supplied_t_s_facts hn fS ht
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨⟨ideal, hmax, h2⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2
  obtain ⟨F', hF', hF'fin, ρ, hcard, -, -, -, hφ1, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam,
      hdeg, hvalues⟩ :=
    Principal.actual_simple_layer_characteristic_valuation_degree_formulas hGnonab n hn S fS t ht2
      hnonab hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal fS hcentR hval
  have hq1' : Nat.card F' % 4 = 1 := by rw [hcard]; exact hq1
  have he : (if Nat.card F' % 4 = 1 then (1 : ℤ) else -1) = 1 := ite_eq_left_iff.mpr
    (fun h => absurd hq1' h)
  rw [he] at hfam hvalues
  obtain ⟨hδ₁, -, -, -, hf₁, hf₂, hf₃, -, -, hν1, -, -⟩ := hvalues
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hodd, htval, hrel⟩ := hfam
  have hk0 : (0 : ℕ) ∈ Finset.range (2 ^ (n - 3)) := by
    simp only [Finset.mem_range]
    positivity
  have hdeg0 : Module.finrank ℂ (basis.representation principal).vector = 1 := by
    have h1 := (Principal.basis_character_one basis principal).1
    rw [hprincipal, Pi.one_apply] at h1
    exact_mod_cast h1.symm
  have hχ₁deg : Module.finrank ℂ (basis.representation χ₁).vector = (p ^ f) ^ 3 := by
    rw [← hcard]
    exact_mod_cast hf₁
  have hle : p ^ f ≤ (p ^ f) ^ 2 := Nat.le_self_pow two_ne_zero _
  have hχ₂deg : Module.finrank ℂ (basis.representation χ₂).vector = (p ^ f) ^ 2 - p ^ f + 1 := by
    have h : ((Module.finrank ℂ (basis.representation χ₂).vector : ℕ) : ℤ) =
        (((p ^ f) ^ 2 - p ^ f + 1 : ℕ) : ℤ) := by
      rw [hf₂, hcard]
      push_cast [Nat.cast_sub hle]
      ring
    exact_mod_cast h
  have hχ₃deg : Module.finrank ℂ (basis.representation χ₃).vector =
      p ^ f * ((p ^ f) ^ 2 - p ^ f + 1) := by
    have h : ((Module.finrank ℂ (basis.representation χ₃).vector : ℕ) : ℤ) =
        ((p ^ f * ((p ^ f) ^ 2 - p ^ f + 1) : ℕ) : ℤ) := by
      rw [hf₃, hcard]
      push_cast [Nat.cast_sub hle]
      ring
    exact_mod_cast h
  refine ⟨⟨χ₁, ν 0, hχ₁deg, ?_, Or.inr ?_, ?_⟩, ?_⟩
  · have h1 := (Principal.basis_character_one basis (ν 0)).1
    rw [hν1 0 hk0, hcard] at h1
    have h : ((Module.finrank ℂ (basis.representation (ν 0)).vector : ℕ) : ℂ) =
        (((p ^ f) ^ 3 + 1 : ℕ) : ℂ) := by
      rw [← h1]
      push_cast
      ring
    exact_mod_cast h
  · have h := (htval 1 (by rw [orderOf_one]; exact odd_one)).2.2.2.2.2 0 hk0
    rw [OneMemClass.coe_one, mul_one] at h
    rw [h, hφ1, hδ₁, hcard]
    push_cast
    ring
  · intro g hg
    rw [(hrel g hg).2.1 0 hk0, hδ₁]
    push_cast
    ring
  · intro χ hreal hoddχ
    have hχB := Principal.real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal
      principal hprincipal χ hreal hoddχ
    rcases (hodd χ hχB).mp hoddχ with rfl | rfl | rfl | rfl
    · exact Or.inl hdeg0
    · exact Or.inr (Or.inl hχ₁deg)
    · exact Or.inr (Or.inr (Or.inl hχ₂deg))
    · exact Or.inr (Or.inr (Or.inr hχ₃deg))

end CFSG.Semidihedral.UnitaryBranch
