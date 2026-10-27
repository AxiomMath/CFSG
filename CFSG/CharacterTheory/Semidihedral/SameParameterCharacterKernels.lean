module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerCharacteristicValuation
public import CFSG.CharacterTheory.Semidihedral.SameParameterSections

public section

open scoped Classical

namespace CFSG.Semidihedral.SameParameterCharacterKernels

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal CFSG.Open
  CFSG.Semidihedral.ActualSimpleLayerLocalPackage

variable {G : Type*} [Group G] [Fintype G]

theorem principal_block_kills_normal_odd_subgroup
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    (c : basis.index)
    (hc : c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    N ≤ MonoidHom.ker (basis.representation c).representation := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  obtain ⟨quotientBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := G ⧸ N)
  obtain ⟨quotientPrincipal, hquotientPrincipal⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible quotientBasis
      (principalFiniteComplexRepresentation (G ⧸ N))
      (principalFiniteComplexRepresentation_isIrreducible (G ⧸ N))
  rw [principalFiniteComplexRepresentation_character] at hquotientPrincipal
  have hprincipalKernel : N ≤ MonoidHom.ker (basis.representation principal).representation := by
    apply CFSG.LyonsUnitaryFour.le_ker_of_character_eq_degree
    intro x _
    change (basis.representation principal).character x =
      (basis.representation principal).character 1
    simp only [hprincipal, Pi.one_apply]
  have hnot : ¬ 2 ∣ Nat.card N :=
    Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_two_left.mpr hN)
  exact (normal_prime_kernel_principal_block_inflation basis ideal 2 N hnot quotientBasis
    principal hprincipal quotientPrincipal hquotientPrincipal).2.2.1
      principal hprincipalKernel c hc

theorem principal_block_kills_odd_core
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (c : basis.index)
    (hc : c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    CFSG.pPrimeCore 2 G ≤ MonoidHom.ker (basis.representation c).representation := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact principal_block_kills_normal_odd_subgroup basis ideal principal hprincipal
    (CFSG.pPrimeCore 2 G) (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2))) c hc

omit [Fintype G] in
theorem involution_isConj_supplied [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (x : G) (hx : orderOf x = 2) : IsConj x t :=
  (InvolutionFusion.ambient_involution_isConj_z n hn S fS hG x hx).trans
    (InvolutionFusion.ambient_involution_isConj_z n hn S fS hG t ht).symm

omit [Fintype G] in
theorem involution_not_mem_kernel [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (data : FiniteComplexRepresentation G) (htrace : data.character t ≠ data.character 1)
    (x : G) (hx : orderOf x = 2) : x ∉ MonoidHom.ker data.representation := by
  intro hmem
  apply htrace
  have hconj := SameParameterSections.character_eq_of_isConj data
    (involution_isConj_supplied n hn S fS hG t ht x hx)
  calc
    data.character t = data.character x := hconj.symm
    _ = data.character 1 := by
      change LinearMap.trace ℂ data.vector (data.representation x) =
        LinearMap.trace ℂ data.vector (data.representation 1)
      rw [MonoidHom.mem_ker.mp hmem, data.representation.map_one]

omit [Fintype G] in
theorem odd_card_of_no_involution [Finite G] (N : Subgroup G)
    (hN : ∀ x : G, x ∈ N → orderOf x ≠ 2) : Odd (Nat.card N) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Nat.coprime_two_left.mp
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro hdiv
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hdiv
  exact hN x x.property (by simpa only [Subgroup.orderOf_coe] using hx)

omit [Fintype G] in
theorem kernel_odd_card [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (data : FiniteComplexRepresentation G) (htrace : data.character t ≠ data.character 1) :
    Odd (Nat.card (MonoidHom.ker data.representation)) := by
  apply odd_card_of_no_involution
  intro x hx hord
  exact involution_not_mem_kernel n hn S fS hG t ht data htrace x hord hx

omit [Fintype G] in
theorem kernel_le_odd_core [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (data : FiniteComplexRepresentation G) (htrace : data.character t ≠ data.character 1) :
    MonoidHom.ker data.representation ≤ CFSG.pPrimeCore 2 G := by
  exact le_sSup ⟨MonoidHom.normal_ker _, Nat.coprime_two_left.mpr
    (kernel_odd_card n hn S fS hG t ht data htrace)⟩

theorem regular_second_degree_gt (q : ℕ) (hq : 5 ≤ q) (e : ℤ) (he : e = 1 ∨ e = -1) :
    (q : ℤ) < (q : ℤ) ^ 2 - e * q + 1 := by
  have hqZ : (5 : ℤ) ≤ q := by exact_mod_cast hq
  rcases he with rfl | rfl <;> nlinarith [sq_nonneg ((q : ℤ) - 2)]

theorem actual_regular_second_character_values {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (t s : G)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (p q k : ℕ) (hq : 5 ≤ q) (e : ℤ) (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
      q e k φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hvalues : ActualPrincipalCharacteristicValues basis t s p q k e δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν) :
    (basis.representation χ₂).character t = (e : ℂ) * q ∧
    (basis.representation χ₂).character 1 = (q : ℂ) ^ 2 - e * q + 1 ∧
    (q : ℤ) < (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) ∧
    (basis.representation χ₂).character t ≠ (basis.representation χ₂).character 1 := by
  obtain ⟨hφ, hδ₁, -, -, -, -, -, -, -, -, -, -, -, -, hty, -⟩ := hfamily
  obtain ⟨hδ₁e, hδ₂, -, -, -, hdegree, -, -, -, -, -, -⟩ := hvalues
  have he : e = 1 ∨ e = -1 := by rwa [hδ₁e] at hδ₁
  obtain ⟨lφ, -, -, hφchar, hφdegree, -⟩ := hφ
  have hφone : φ 1 = q := by
    rw [← hφchar, (basis_character_one localBasis lφ).1, hφdegree]
  have htvalue : (basis.representation χ₂).character t = (e : ℂ) * q := by
    simpa [hδ₂, hφone] using (hty (1 : C t) (by simp)).2.1
  have hdegreeC : (Module.finrank ℂ (basis.representation χ₂).vector : ℂ) =
      (q : ℂ) ^ 2 - e * q + 1 := by exact_mod_cast hdegree
  have hone : (basis.representation χ₂).character 1 = (q : ℂ) ^ 2 - e * q + 1 :=
    (basis_character_one basis χ₂).1.trans hdegreeC
  have hgt := regular_second_degree_gt q hq e he
  refine ⟨htvalue, hone, by rwa [hdegree], ?_⟩
  intro hequal
  rw [htvalue, hone] at hequal
  have hequalZ : e * (q : ℤ) = (q : ℤ) ^ 2 - e * q + 1 := by exact_mod_cast hequal
  rcases he with rfl | rfl <;> simp at hequalZ <;> nlinarith

theorem actual_regular_second_character_kernel {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (p q : ℕ) (hq : 5 ≤ q) (e : ℤ) (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
      q e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hvalues : ActualPrincipalCharacteristicValues basis t (fS (s n) : G) p q
      (2 ^ (n - 3)) e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    MonoidHom.ker (basis.representation χ₂).representation = CFSG.pPrimeCore 2 G := by
  have htrace := (actual_regular_second_character_values basis ideal principal t
    (fS (s n) : G) localBasis localPrincipal p q (2 ^ (n - 3)) hq e φ δ₁ δ₂ δ₃ δ₄
    χ₁ χ₂ χ₃ χ₄ ψ ν hfamily hvalues).2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hblock, -, -, -, -⟩ := hfamily
  have hχ₂ : χ₂ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    rw [hblock]
    simp
  exact le_antisymm
    (kernel_le_odd_core n hn S fS hG t ht (basis.representation χ₂) htrace)
    (principal_block_kills_odd_core basis ideal principal hprincipal χ₂ hχ₂)

omit [Fintype G] in
theorem restrictRepresentation_kernel (U : Subgroup G) (data : FiniteComplexRepresentation G) :
    MonoidHom.ker (SameParameterSections.restrictRepresentation U data).representation =
      (MonoidHom.ker data.representation).comap U.subtype := by
  ext x
  rfl

omit [Fintype G] in
theorem mem_kernel_iff_character_eq_degree [Finite G] (data : FiniteComplexRepresentation G)
    (x : G) : x ∈ MonoidHom.ker data.representation ↔ data.character x = data.character 1 := by
  constructor
  · intro hx
    change LinearMap.trace ℂ data.vector (data.representation x) =
      LinearMap.trace ℂ data.vector (data.representation 1)
    rw [MonoidHom.mem_ker.mp hx, data.representation.map_one]
  · intro hx
    by_contra hnot
    exact character_ne_one_of_not_mem_ker data hnot hx

omit [Fintype G] in
theorem kernel_eq_of_character_eq [Finite G] (data data' : FiniteComplexRepresentation G)
    (hcharacter : data.character = data'.character) :
    MonoidHom.ker data.representation = MonoidHom.ker data'.representation := by
  ext x
  rw [mem_kernel_iff_character_eq_degree, mem_kernel_iff_character_eq_degree, hcharacter]

theorem restriction_kernel_eq_of_basis_character (U : Subgroup G)
    (data : FiniteComplexRepresentation G) (basisU : FiniteIrreducibleCharacterBasis U)
    (α : basisU.index)
    (hcharacter : (SameParameterSections.restrictRepresentation U data).character =
      (basisU.representation α).character) :
    (MonoidHom.ker data.representation).comap U.subtype =
      MonoidHom.ker (basisU.representation α).representation := by
  rw [← restrictRepresentation_kernel]
  exact kernel_eq_of_character_eq _ _ hcharacter

theorem actual_regular_odd_core_intersection {G : Type} [Group G] [Fintype G]
    (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (fSU : SemidihedralGroup m ≃* SU)
    (hG : ∀ V : Subgroup G, V.index ≠ 2) (hU : ∀ V : Subgroup U, V.index ≠ 2)
    (basis : FiniteIrreducibleCharacterBasis G) (basisU : FiniteIrreducibleCharacterBasis U)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (principalU : basisU.index)
    (hprincipal : (basis.representation principal).character = 1)
    (hprincipalU : (basisU.representation principalU).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (localBasisU : FiniteIrreducibleCharacterBasis (C t))
    (localPrincipal : localBasis.index) (localPrincipalU : localBasisU.index)
    (p q : ℕ) (hq : 5 ≤ q) (e : ℤ) (φ : C (t : G) → ℂ) (φU : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ ε₁ ε₂ ε₃ ε₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (α₁ α₂ α₃ α₄ : basisU.index)
    (ψ ν : ℕ → basis.index) (ψU νU : ℕ → basisU.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal (t : G) localBasis
      localPrincipal q e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hvalues : ActualPrincipalCharacteristicValues basis (t : G) (fS (s n) : G) p q
      (2 ^ (n - 3)) e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hfamilyU : ActualPrincipalBlockFamily basisU ideal principalU t localBasisU
      localPrincipalU q e (2 ^ (m - 3)) φU ε₁ ε₂ ε₃ ε₄ α₁ α₂ α₃ α₄ ψU νU)
    (hvaluesU : ActualPrincipalCharacteristicValues basisU t (fSU (s m) : U) p q
      (2 ^ (m - 3)) e ε₁ ε₂ ε₃ ε₄ α₁ α₂ α₃ α₄ ψU νU)
    (hrestriction : (SameParameterSections.restrictRepresentation U
      (basis.representation χ₂)).character = (basisU.representation α₂).character) :
    CFSG.pPrimeCore 2 U = (CFSG.pPrimeCore 2 G).comap U.subtype ∧
      (CFSG.pPrimeCore 2 U).map U.subtype = U ⊓ CFSG.pPrimeCore 2 G := by
  have htG : orderOf (t : G) = 2 := by simpa only [Subgroup.orderOf_coe] using ht
  have hkernel := actual_regular_second_character_kernel n hn S fS hG (t : G) htG basis
    ideal principal hprincipal localBasis localPrincipal p q hq e φ δ₁ δ₂ δ₃ δ₄
    χ₁ χ₂ χ₃ χ₄ ψ ν hfamily hvalues
  have hkernelU := actual_regular_second_character_kernel m hm SU fSU hU t ht basisU
    ideal principalU hprincipalU localBasisU localPrincipalU p q hq e φU ε₁ ε₂ ε₃ ε₄
    α₁ α₂ α₃ α₄ ψU νU hfamilyU hvaluesU
  have hcomap := restriction_kernel_eq_of_basis_character U (basis.representation χ₂)
    basisU α₂ hrestriction
  rw [hkernel, hkernelU] at hcomap
  refine ⟨hcomap.symm, ?_⟩
  rw [hcomap.symm]
  change ((CFSG.pPrimeCore 2 G).subgroupOf U).map U.subtype = U ⊓ CFSG.pPrimeCore 2 G
  rw [Subgroup.subgroupOf_map_subtype, inf_comm]

end CFSG.Semidihedral.SameParameterCharacterKernels
