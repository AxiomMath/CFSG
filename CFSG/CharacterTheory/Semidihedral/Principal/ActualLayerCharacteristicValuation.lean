module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerOrderFormulas
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerRotationCongruencesSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.SignedDegreeNumerics
public import CFSG.CharacterTheory.Semidihedral.Principal.SignedDegreeCubic

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage
  CFSG.LyonsUnitaryFour CFSG.Open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Wreathed

@[expose] def ActualPrincipalCharacteristicValues {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (t s : G) (p q k : ℕ) (e : ℤ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index) : Prop :=
  δ₁ = e ∧ δ₂ = -1 ∧ δ₃ = -e ∧ δ₄ = 1 ∧
  (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) = (q : ℤ) ^ 3 ∧
  (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) = (q : ℤ) ^ 2 - e * q + 1 ∧
  (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) = q * ((q : ℤ) ^ 2 - e * q + 1) ∧
  (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) = (q : ℤ) ^ 2 - e * q ∧
  (∀ j ∈ Finset.Icc 1 (k - 1), (basis.representation (ψ j)).character 1 = (q : ℂ) ^ 3 + e) ∧
  (∀ i ∈ Finset.range k, (basis.representation (ν i)).character 1 = (q : ℂ) ^ 3 + e) ∧
  (Nat.card G : ℚ) = (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℚ) ^ 3 /
      (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) :
        Subgroup G) : ℚ) ^ 2 * (((q : ℚ) ^ 2 - e * q + 1) / ((q : ℚ) - e) ^ 2) ∧
  (padicValNat p (Nat.card G) : ℤ) =
    3 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) : ℤ) -
      2 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({s} : Set G) : Subgroup G)) : ℤ)


theorem characteristic_order_factor {q e : ℚ} (he : e = 1 ∨ e = -1) (hq : 1 < q) :
    q ^ 3 * (q ^ 3 + e) / (q ^ 3 - e * e * q) ^ 2 * ((q + e) / q) =
      (q ^ 2 - e * q + 1) / (q - e) ^ 2 := by
  have hq0 : q ≠ 0 := by linarith
  have h1 : q - 1 ≠ 0 := by linarith
  rcases he with rfl | rfl
  · have h3 : (q ^ 3 - 1 * 1 * q) = q * (q - 1) * (q + 1) := by ring
    rw [h3, div_mul_div_comm, div_eq_div_iff (by positivity) (pow_ne_zero 2 h1)]
    ring
  · have h3 : (q ^ 3 - (-1) * (-1) * q) = q * (q - 1) * (q + 1) := by ring
    rw [h3, div_mul_div_comm, div_eq_div_iff (by positivity) (pow_ne_zero 2 (by linarith))]
    ring

theorem actual_principal_characteristic_values_of_family {G : Type} [Group G] [Fintype G]
    (hindex : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {t : G} (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (q : ℕ) (hq : q = p ^ f) (e : ℤ)
    (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    {S : Sylow 2 G} (e' : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t)
    (hOF : ActualPrincipalOrderFormulas G t (e' (s n) : G) q e δ₁ δ₂
      (Module.finrank ℂ (basis.representation χ₁).vector)
      (Module.finrank ℂ (basis.representation χ₂).vector))
    (hval : 3 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) : ℤ) -
        2 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer ({(e' (s n) : G)} : Set G) : Subgroup G)) : ℤ) ≤
      padicValNat p (Nat.card G)) :
    ActualPrincipalCharacteristicValues basis t (e' (s n) : G) p q (2 ^ (n - 3)) e δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν := by
  obtain ⟨hq3, hqodd⟩ := three_le_and_odd_of_prime_pow hp hpodd hf
  rw [← hq] at hq3 hqodd
  have he' : e = 1 ∨ e = -1 := by
    rw [he]
    split_ifs <;> simp
  have he1 : q % 4 = 1 → e = 1 := fun h => by rw [he, ite_eq_left h]
  have he3 : q % 4 = 3 → e = -1 := fun h => by rw [he, ite_eq_right (by omega)]
  obtain ⟨-, hc₁, hc₂, hc₃⟩ := actual_principal_rotation_values_and_congruences hindex hn ht
    hnonab basis ideal principal hprincipal localBasis localPrincipal q hq3 hqodd e he1 he3 φ
    δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg e' hcent
  obtain ⟨-, hδ₁, hδ₂, hδ₃, hδ₄, hnd, -, -, -, -, -, hB, -, hodd, -, hrel⟩ := hfam
  obtain ⟨hf₁1, hf₂1, hf₃1, hf₄1, hsign, hδ₄₂, hf₄₂, hprod, -⟩ := hdeg
  obtain ⟨hden₁, hden₂, hg₁, hg₂⟩ := hOF
  set f₁ := Module.finrank ℂ (basis.representation χ₁).vector with hf₁def
  set f₂ := Module.finrank ℂ (basis.representation χ₂).vector with hf₂def
  set f₃ := Module.finrank ℂ (basis.representation χ₃).vector with hf₃def
  set f₄ := Module.finrank ℂ (basis.representation χ₄).vector with hf₄def
  set c := Nat.card (Subgroup.centralizer ({t} : Set G)) with hcdef
  set d := Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
    Subgroup.centralizer ({(e' (s n) : G)} : Set G) : Subgroup G) with hddef
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index),
      c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have ho₁ : Odd f₁ := (hodd χ₁ (hmem χ₁ (by simp))).mpr (Or.inr (Or.inl rfl))
  have ho₂ : Odd f₂ := (hodd χ₂ (hmem χ₂ (by simp))).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have ho₃ : Odd f₃ := (hodd χ₃ (hmem χ₃ (by simp))).mpr (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨hψ1, hν1, hrel1, -⟩ := hrel 1 (by simp)
  rw [(basis_character_one basis χ₁).1, (basis_character_one basis χ₂).1,
    (basis_character_one basis χ₃).1] at hrel1
  have hsum : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0 := by
    have h : (((1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ : ℤ)) : ℂ) = 0 := by
      push_cast
      exact hrel1
    exact_mod_cast h
  have hprodZ : (f₁ : ℤ) * f₂ = (q : ℤ) ^ 2 * f₃ := by exact_mod_cast hprod
  have hden₁Z : (f₁ : ℤ) - e * δ₁ * q ≠ 0 := fun h => hden₁ (by exact_mod_cast h)
  have hden₂Z : (f₂ : ℤ) + e * δ₂ * q ≠ 0 := fun h => hden₂ (by exact_mod_cast h)
  have hf₁δ : (0 : ℤ) < f₁ + δ₁ := by rcases hδ₁ with rfl | rfl <;> omega
  have hf₂δ : (0 : ℤ) < f₂ + δ₂ := by rcases hδ₂ with rfl | rfl <;> omega
  have hdiv := principal_order_valuation_forces_cubic_degree hp hpodd hf hq he' hδ₁ hδ₂
    (f₁ := (f₁ : ℤ)) (f₂ := (f₂ : ℤ)) (f₃ := (f₃ : ℤ)) (c := c) (d := d) (g := Nat.card G)
    (by omega) (by omega) (by omega) Nat.card_pos Nat.card_pos Nat.card_pos hf₁δ hf₂δ hprodZ
    hden₁Z hden₂Z (by push_cast; exact hg₁) (by push_cast; exact hg₂) hval
  have he4 : (q : ℤ) % 4 = 1 ∧ e = 1 ∨ (q : ℤ) % 4 = 3 ∧ e = -1 := by
    have h2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
    rcases Nat.lt_or_ge (q % 4) 2 with h | h
    · left
      have h1 : q % 4 = 1 := by omega
      exact ⟨by omega, he1 h1⟩
    · right
      have h3 : q % 4 = 3 := by omega
      exact ⟨by omega, he3 h3⟩
  obtain ⟨hδ₁e, hδ₂m, hδ₃e, hf₁v, hf₂v, hf₃v, -, -⟩ :=
    signed_degree_product_cubic_divisibility_rigidity (q : ℤ) e f₁ f₂ f₃ δ₁ δ₂ δ₃
      (by exact_mod_cast hq3) (by exact_mod_cast hqodd) he4 (by exact_mod_cast hf₁1)
      (by exact_mod_cast hf₂1) (by exact_mod_cast hf₃1) (by exact_mod_cast ho₁)
      (by exact_mod_cast ho₂) (by exact_mod_cast ho₃) hsign hsum hprodZ hc₁ hc₂ hc₃ hdiv
  have hf₁C : ((f₁ : ℕ) : ℂ) = (q : ℂ) ^ 3 := by exact_mod_cast hf₁v
  have hf₁Q : ((f₁ : ℕ) : ℚ) = (q : ℚ) ^ 3 := by exact_mod_cast hf₁v
  have hqQ : (1 : ℚ) < q := by exact_mod_cast (show 1 < q by omega)
  have hGformula : (Nat.card G : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 *
      (((q : ℚ) ^ 2 - e * q + 1) / ((q : ℚ) - e) ^ 2) := by
    have heQ : (e : ℚ) = 1 ∨ (e : ℚ) = -1 := by
      rcases he' with h | h <;> [left; right] <;> rw [h] <;> push_cast <;> rfl
    rw [hg₁, hf₁Q, hδ₁e, mul_assoc, characteristic_order_factor heQ hqQ]
  refine ⟨hδ₁e, hδ₂m, hδ₃e, by rw [hδ₄₂, hδ₂m]; norm_num, hf₁v, hf₂v, hf₃v,
    by rw [hf₄₂, hf₂v, hδ₂m]; ring, ?_, ?_, hGformula, ?_⟩
  · intro j hj
    rw [hψ1 j hj, (basis_character_one basis χ₁).1, hf₁C, hδ₁e]
  · intro i hi
    rw [hν1 i hi, (basis_character_one basis χ₁).1, hf₁C, hδ₁e]
  ·
    have : Fact p.Prime := ⟨hp⟩
    have hq0Z : ((q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hpq : (p : ℤ) ∣ (q : ℤ) := by
      rw [hq]
      push_cast
      exact dvd_pow_self _ (by omega)
    have hA0 : ((q : ℤ) ^ 2 - e * q + 1) ≠ 0 := by
      rcases he' with rfl | rfl <;> nlinarith [hq3]
    have hC0 : ((q : ℤ) - e) ≠ 0 := by rcases he' with rfl | rfl <;> omega
    have hvA : padicValInt p ((q : ℤ) ^ 2 - e * q + 1) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro h
      have h1 : (p : ℤ) ∣ (q : ℤ) ^ 2 - e * q := by
        rw [show (q : ℤ) ^ 2 - e * q = (q : ℤ) * (q - e) by ring]
        exact dvd_mul_of_dvd_left hpq _
      have : (p : ℤ) ∣ 1 := by
        have := dvd_sub h h1
        rwa [show (q : ℤ) ^ 2 - e * q + 1 - ((q : ℤ) ^ 2 - e * q) = 1 by ring] at this
      exact not_prime_dvd_sign hp (Or.inl rfl) this
    have hvC : padicValInt p ((q : ℤ) - e) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro h
      have he'' : -e = 1 ∨ -e = -1 := by rcases he' with rfl | rfl <;> simp
      exact not_prime_dvd_sign hp he'' (by
        have := dvd_sub h hpq
        rwa [show (q : ℤ) - e - q = -e by ring] at this)
    have h := padicValNat_order_formula (p := p) (c := c) (d := d) (g := Nat.card G)
      (A := (q : ℤ) ^ 2 - e * q + 1) (B := 1) (C := (q : ℤ) - e) (E := 1) (Q := 1)
      Nat.card_pos.ne' Nat.card_pos.ne' hA0 one_ne_zero hC0 one_ne_zero one_ne_zero
      (by rw [hGformula]; push_cast; ring)
    rw [hvA, hvC, padicValInt.one] at h
    linarith


theorem actual_nonsimple_layer_characteristic_valuation_degree_formulas
    {G : Type} [Group G]
    [Fintype G]
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
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {S : Sylow 2 G} (e' : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t)
    (hval : 3 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) : ℤ) -
        2 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer ({(e' (s n) : G)} : Set G) : Subgroup G)) : ℤ) ≤
      padicValNat p (Nat.card G)) :
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
        ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ∧
        ActualPrincipalCharacteristicValues basis t (e' (s n) : G) p (Nat.card F) (2 ^ (n - 3))
          e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) := by
  obtain ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hlin, hrest⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S0 f0 hG t ht hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  refine ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hlin, ?_⟩
  intro φ e
  obtain ⟨hφ1, hφnc, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg, -, hOF⟩ := hrest
  exact ⟨hφ1, hφnc, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg,
    actual_principal_characteristic_values_of_family hG hn ht hnonab basis ideal principal
      hprincipal localBasis localPrincipal hp hpodd hf (Nat.card F) hcard e rfl φ δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg e' hcent (hOF S e' hcent) hval⟩

theorem actual_simple_layer_characteristic_valuation_degree_formulas
    {G : Type} [Group G]
    [Fintype G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
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
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {S : Sylow 2 G} (e' : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t)
    (hval : 3 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) : ℤ) -
        2 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer ({(e' (s n) : G)} : Set G) : Subgroup G)) : ℤ) ≤
      padicValNat p (Nat.card G)) :
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
        ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ∧
        ActualPrincipalCharacteristicValues basis t (e' (s n) : G) p (Nat.card F) (2 ^ (n - 3))
          e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :=
  actual_nonsimple_layer_characteristic_valuation_degree_formulas n hn S0 f0
    (index_ne_two_of_isSimpleGroup hGnonab) t ht hnonab hcentral hnc p f hp hpodd hf hmodel ideal
    basis principal hprincipal localBasis localPrincipal hlocalPrincipal e' hcent hval

end CFSG.Semidihedral.Principal
