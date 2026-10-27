module

public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootColumns
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityConstituents

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

variable {G : Type} [Group G] [Fintype G]

theorem actual_root_three_nontrivial_principal_labels
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    ∃ (α : Fin 3 → basis.index) (β : Fin 3 → ℤ), Function.Injective α ∧
      (∀ i, α i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
        α i ≠ principal ∧
        (basis.representation (α i)).character ∈ BlocksIrr G ∧
        (basis.representation (α i)).character ∈ BlocksPrincipalBlock ideal G ∧
        (basis.representation (α i)).character ≠ 1 ∧
        (β i = 1 ∨ β i = -1) ∧
        oddPowerCoefficient (basis.representation (α i)) (actualRoot S e) root (2 ^ n) = β i) ∧
      (∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddPowerCoefficient (basis.representation ψ) (actualRoot S e) root (2 ^ n) ≠ 0 ↔
          ψ = principal ∨ ∃ i, α i = ψ) ∧
      oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) =
        (1 : G → ℂ) + ∑ i, β i • (basis.representation (α i)).character ∧
      oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) ∈
        BlocksVChar G ∧
      (∀ g ∉ squareRootSection (actualRoot S e),
        oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) g = 0) ∧
      (1 : ℤ) + ∑ i, β i * (Module.finrank ℂ (basis.representation (α i)).vector : ℤ) = 0 := by
  let I := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  let c : basis.index → ℤ := fun χ =>
    oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n)
  let T := I.filter (fun χ => c χ ≠ 0)
  have hhalf : 0 < 2 ^ n / 2 := by
    have hpow : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hfour := (CFSG.Wreathed.ConditionalSquareRoot.actualRoot_signed_even_columns
    n hn S e basis ideal principal hprincipal hroot).2.2.2.2.2 0 hhalf
  have hcdef : ∀ χ, c χ = signedEvenEigenmultiplicity
      (basis.representation χ) (actualRoot S e) root (2 ^ n) 0 := by
    intro χ
    simp only [c, oddPowerCoefficient, signedEvenEigenmultiplicity, mul_zero, zero_add]
  have hTcard : T.card = 4 := by
    simpa only [T, I, hcdef] using hfour.1
  have hcunits : ∀ χ ∈ I, c χ = 0 ∨ c χ = 1 ∨ c χ = -1 := by
    simpa only [I, hcdef] using hfour.2
  have hcp : c principal = 1 := actual_root_odd_power_principal_coefficient
    n hn S e basis principal hprincipal root hroot
  have hpT : principal ∈ T := Finset.mem_filter.mpr
    ⟨coefficientBlock_self_mem basis _ principal, by rw [hcp]; omega⟩
  have hUcard : (T.erase principal).card = 3 := by
    rw [Finset.card_erase_of_mem hpT, hTcard]
  obtain ⟨A, B, D, hAB, hAD, hBD, hU⟩ := Finset.card_eq_three.mp hUcard
  have hAmem : A ∈ T.erase principal := by rw [hU]; simp
  have hBmem : B ∈ T.erase principal := by rw [hU]; simp
  have hDmem : D ∈ T.erase principal := by rw [hU]; simp
  have hAp : A ≠ principal := (Finset.mem_erase.mp hAmem).1
  have hBp : B ≠ principal := (Finset.mem_erase.mp hBmem).1
  have hDp : D ≠ principal := (Finset.mem_erase.mp hDmem).1
  have hT : T = {principal, A, B, D} := by
    rw [← Finset.insert_erase hpT, hU]
  let α : Fin 3 → basis.index := ![A, B, D]
  let β : Fin 3 → ℤ := fun i => c (α i)
  have hαinj : Function.Injective α := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [α]
  have hαmem : ∀ i, α i ∈ T.erase principal := by
    intro i
    fin_cases i <;> simp [α, hU]
  have hαdata : ∀ i, α i ∈ I ∧ α i ≠ principal ∧
      (basis.representation (α i)).character ∈ BlocksIrr G ∧
      (basis.representation (α i)).character ∈ BlocksPrincipalBlock ideal G ∧
      (basis.representation (α i)).character ≠ 1 ∧
      (β i = 1 ∨ β i = -1) ∧ c (α i) = β i := by
    intro i
    obtain ⟨hip, hiT⟩ := Finset.mem_erase.mp (hαmem i)
    obtain ⟨hiI, hic⟩ := Finset.mem_filter.mp hiT
    have hb : (basis.representation (α i)).character ∈ BlocksPrincipalBlock ideal G := by
      change (basis.representation (α i)).character ∈ BlocksBlockOf ideal G (1 : G → ℂ)
      rw [← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal]
      exact ⟨α i, hiI, rfl⟩
    refine ⟨hiI, hip, CFSG.BlockBasics.basis_character_mem_irr basis _, hb, ?_, ?_, rfl⟩
    · intro heq
      exact hip (basis.distinct (heq.trans hprincipal.symm))
    · rcases hcunits (α i) hiI with h0 | h1 | hm1
      · exact (hic h0).elim
      · exact Or.inl h1
      · exact Or.inr hm1
  have hsupport : ∀ ψ ∈ I, c ψ ≠ 0 ↔ ψ = principal ∨ ∃ i, α i = ψ := by
    intro ψ hψ
    have hmem : c ψ ≠ 0 ↔ ψ ∈ T := by simp only [T, Finset.mem_filter, hψ, true_and]
    rw [hmem, hT]
    constructor
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨0, h.symm⟩
      · exact Or.inr ⟨1, h.symm⟩
      · exact Or.inr ⟨2, h.symm⟩
    · rintro (h | ⟨i, h⟩)
      · simp [h]
      · fin_cases i <;> simp_all [α]
  have hsum : oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) =
      (1 : G → ℂ) + ∑ i, β i • (basis.representation (α i)).character := by
    ext g
    have hrestrict : (∑ χ ∈ T, (c χ : ℂ) * (basis.representation χ).character g) =
        ∑ χ ∈ I, (c χ : ℂ) * (basis.representation χ).character g := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro χ hχ hnT
      have hc0 : c χ = 0 := by
        by_contra hc0
        exact hnT (Finset.mem_filter.mpr ⟨hχ, hc0⟩)
      rw [hc0, Int.cast_zero, zero_mul]
    change (∑ χ ∈ I, (c χ : ℂ) * (basis.representation χ).character g) = _
    rw [← hrestrict, hT]
    rw [Finset.sum_insert (by simp [Ne.symm hAp, Ne.symm hBp, Ne.symm hDp]),
      Finset.sum_insert (by simp [hAB, hAD]), Finset.sum_insert (by simp [hBD]),
      Finset.sum_singleton, hcp]
    simp [hprincipal, α, β, Fin.sum_univ_three, Pi.add_apply, zsmul_eq_mul]
    ring
  obtain ⟨hvirtual, hoff, hzero, _, _⟩ := actual_root_integral_odd_power_column
    n hn S e basis ideal principal hprincipal root hroot
  have hdegree : (1 : ℤ) + ∑ i, β i *
      (Module.finrank ℂ (basis.representation (α i)).vector : ℤ) = 0 := by
    have h := congrFun hsum 1
    rw [hzero] at h
    simp only [Pi.add_apply, Pi.one_apply, Finset.sum_apply, zsmul_eq_mul,
      Pi.mul_apply, Pi.intCast_apply, FiniteComplexRepresentation.character,
      Representation.char_one] at h
    exact_mod_cast h.symm
  exact ⟨α, β, hαinj, hαdata, hsupport, hsum, hvirtual, hoff, hdegree⟩

theorem actual_root_three_labels_and_genuine_section_detection
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    ∃ (α : Fin 3 → basis.index) (β : Fin 3 → ℤ), Function.Injective α ∧
      (∀ i, α i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
        α i ≠ principal ∧
        (basis.representation (α i)).character ∈ BlocksIrr G ∧
        (basis.representation (α i)).character ∈ BlocksPrincipalBlock ideal G ∧
        (basis.representation (α i)).character ≠ 1 ∧
        (β i = 1 ∨ β i = -1) ∧
        oddPowerCoefficient (basis.representation (α i)) (actualRoot S e) root (2 ^ n) = β i) ∧
      (∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddPowerCoefficient (basis.representation ψ) (actualRoot S e) root (2 ^ n) ≠ 0 ↔
          ψ = principal ∨ ∃ i, α i = ψ) ∧
      oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) =
        (1 : G → ℂ) + ∑ i, β i • (basis.representation (α i)).character ∧
      oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) ∈
        BlocksVChar G ∧
      (∀ g ∉ squareRootSection (actualRoot S e),
        oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) g = 0) ∧
      ((1 : ℤ) + ∑ i, β i * (Module.finrank ℂ (basis.representation (α i)).vector : ℤ) = 0) ∧
      ∀ θ : FiniteComplexRepresentation.{0, 0} G,
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        ∃ i : Fin 3, β i = -1 ∧ ∃ k : ℕ, 0 < k ∧
          BlocksInnerProduct θ.character (basis.representation (α i)).character = (k : ℂ) ∧
          Module.finrank ℂ (basis.representation (α i)).vector ≤ Module.finrank ℂ θ.vector := by
  obtain ⟨α, β, hα, hdata, hsupport, hsum, hvirtual, hoff, hdegree⟩ :=
    actual_root_three_nontrivial_principal_labels n hn S e basis ideal principal
      hprincipal root hroot
  refine ⟨α, β, hα, hdata, hsupport, hsum, hvirtual, hoff, hdegree, ?_⟩
  intro θ hsection
  obtain ⟨χ, _, hblock, hnontrivial, hc, k, hk, hpair, hdeg⟩ :=
    actual_section_minus_one_has_principal_constituent n hn S e basis ideal principal
      hprincipal root hroot θ hsection
  have hχblock : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    change (basis.representation χ).character ∈ BlocksBlockOf ideal G (1 : G → ℂ) at hblock
    rw [← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal] at hblock
    obtain ⟨ψ, hψ, heq⟩ := hblock
    rwa [basis.distinct heq] at hψ
  have hχp : χ ≠ principal := by
    intro h
    subst χ
    exact hnontrivial hprincipal
  obtain hp | ⟨i, hi⟩ := (hsupport χ hχblock).mp (by omega)
  · exact (hχp hp).elim
  · have hβnegative : β i < 0 := by rw [← (hdata i).2.2.2.2.2.2, hi]; exact hc
    have hβ : β i = -1 := by
      rcases (hdata i).2.2.2.2.2.1 with h | h
      · omega
      · exact h
    exact ⟨i, hβ, k, hk, hi ▸ hpair, hi ▸ hdeg⟩

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
