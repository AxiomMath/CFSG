module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlock

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

section Core

variable {G : Type*} [Group G] [Fintype G]

theorem prime_inversion_family_odd_member_of_real_odd_principal
    (basis : FiniteIrreducibleCharacterBasis G) (ideal₂ : Ideal ComplexAlgebraicIntegers)
    [ideal₂.IsMaximal] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (α₁ α₂ α₃ : basis.index) (hnodup : [principal, α₁, α₂, α₃].Nodup)
    (hodd₂ : ∀ θ, (θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal ∧
        Odd (Module.finrank ℂ (basis.representation θ).vector)) ↔
      θ = principal ∨ θ = α₁ ∨ θ = α₂ ∨ θ = α₃)
    (hf₁ : 1 < Module.finrank ℂ (basis.representation α₁).vector)
    (hf₂ : 1 < Module.finrank ℂ (basis.representation α₂).vector)
    (hf₃ : 1 < Module.finrank ℂ (basis.representation α₃).vector)
    (ε₁ ε₂ ε₃ : ℤ)
    (hrel : 1 + ε₁ * (Module.finrank ℂ (basis.representation α₁).vector : ℤ) +
      ε₂ * (Module.finrank ℂ (basis.representation α₂).vector : ℤ) +
      ε₃ * (Module.finrank ℂ (basis.representation α₃).vector : ℤ) = 0)
    (hrealodd : ∀ θ, (∀ g, starRingEnd ℂ ((basis.representation θ).character g) =
        (basis.representation θ).character g) →
      Odd (Module.finrank ℂ (basis.representation θ).vector) →
      θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal)
    (idealℓ : Ideal ComplexAlgebraicIntegers) [idealℓ.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ idealℓ) ℓ] (hℓ : 7 ≤ ℓ) (P : Sylow ℓ G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 2) :
    ∃ (δ : ℤ) (χ : basis.index) (ψ : ℕ → basis.index),
      (δ = 1 ∨ δ = -1) ∧ χ ≠ principal ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ψ i ≠ principal ∧ ψ i ≠ χ) ∧
      Set.InjOn ψ (Finset.Icc 1 ((ℓ - 1) / 2)) ∧
      coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal =
        insert principal (insert χ ((Finset.Icc 1 ((ℓ - 1) / 2)).image ψ)) ∧
      (∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal, ∀ g : G,
        starRingEnd ℂ ((basis.representation θ).character g) =
          (basis.representation θ).character g) ∧
      (χ = α₁ ∨ χ = α₂ ∨ χ = α₃) ∧
      1 < Module.finrank ℂ (basis.representation χ).vector ∧
      Odd (Module.finrank ℂ (basis.representation χ).vector) ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2),
        (Module.finrank ℂ (basis.representation (ψ i)).vector : ℤ) =
          (Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ ∧
        0 < Module.finrank ℂ (basis.representation (ψ i)).vector ∧
        Even (Module.finrank ℂ (basis.representation (ψ i)).vector)) ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ∀ x : G, ¬ ℓ ∣ orderOf x →
        (basis.representation (ψ i)).character x = (basis.representation χ).character x + δ) ∧
      (∀ j ∈ Finset.Icc 1 (ℓ - 1), ∀ y ∈ Subgroup.centralizer (P : Set G), ¬ ℓ ∣ orderOf y →
        (basis.representation χ).character (u ^ j * y) = δ ∧
        ∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2),
          (basis.representation (ψ i)).character (u ^ j * y) =
            δ * (Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ ((i * j : ℕ) : ℤ) +
              Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ (-((i * j : ℕ) : ℤ)))) ∧
      (∀ z : G, ℓ ∣ orderOf z → ∃ j ∈ Finset.Icc 1 (ℓ - 1),
        ∃ y ∈ Subgroup.centralizer (P : Set G), ¬ ℓ ∣ orderOf y ∧ IsConj z (u ^ j * y)) ∧
      ∀ x₁ x₂ z : G, ¬ ℓ ∣ orderOf x₁ → ¬ ℓ ∣ orderOf x₂ → ℓ ∣ orderOf z →
        ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal,
          (basis.representation θ).character x₁ * (basis.representation θ).character x₂ *
            (basis.representation θ).character z / (basis.representation θ).character 1 =
          ((basis.representation χ).character 1 - (basis.representation χ).character x₁) *
            ((basis.representation χ).character 1 - (basis.representation χ).character x₂) /
              ((basis.representation χ).character 1 *
                ((basis.representation χ).character 1 + δ)) := by
  obtain ⟨δ, χ, ψ, hδ, hχp, hψne, hψinj, hB, hreal, hpos, hdeg, hreg, hvals, hconj, hsum⟩ :=
    prime_order_sylow_inversion_normalizer_exact_principal_block_family basis idealℓ ℓ (by omega)
      principal hprincipal P u hPu hP hindex
  set r := (ℓ - 1) / 2 with hr
  have hr3 : 3 ≤ r := by omega
  have hχB : χ ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal := by
    rw [hB]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hψB : ∀ i ∈ Finset.Icc 1 r,
      ψ i ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal := by
    intro i hi
    rw [hB]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi))
  have hdegZ : ∀ i ∈ Finset.Icc 1 r,
      (Module.finrank ℂ (basis.representation (ψ i)).vector : ℤ) =
        (Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ := by
    intro i hi
    have h := hdeg i hi
    rw [FiniteComplexRepresentation.character, Representation.char_one,
      FiniteComplexRepresentation.character, Representation.char_one] at h
    exact_mod_cast h
  have hmemα : ∀ θ, θ ≠ principal → (∀ g, starRingEnd ℂ ((basis.representation θ).character g) =
      (basis.representation θ).character g) →
      Odd (Module.finrank ℂ (basis.representation θ).vector) → θ = α₁ ∨ θ = α₂ ∨ θ = α₃ := by
    intro θ hθ hθr hθo
    rcases (hodd₂ θ).mp ⟨hrealodd θ hθr hθo, hθo⟩ with h | h
    · exact absurd h hθ
    · exact h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnodup
  obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23⟩ := hnodup
  have heven : Even ((Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ) := by
    by_contra hnot
    have hD : Odd ((Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ) :=
      Int.not_even_iff_odd.mp hnot
    set D := (Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ with hDdef
    have hψα : ∀ i ∈ Finset.Icc 1 r, ψ i = α₁ ∨ ψ i = α₂ ∨ ψ i = α₃ := by
      intro i hi
      refine hmemα (ψ i) (hψne i hi).1 (hreal (ψ i) (hψB i hi)) ?_
      have h := hdegZ i hi
      rw [← h] at hD
      exact Int.odd_coe_nat _ |>.mp hD
    set T := (Finset.Icc 1 r).image ψ with hT
    have hTsub : T ⊆ {α₁, α₂, α₃} := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rcases hψα i hi with h | h | h <;> simp [h]
    have hTcard : T.card = r := by
      rw [hT, Finset.card_image_of_injOn hψinj, Nat.card_Icc]
      omega
    have hαcard : ({α₁, α₂, α₃} : Finset basis.index).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23.1]
    have hTeq : T = {α₁, α₂, α₃} :=
      Finset.eq_of_subset_of_card_le hTsub (by rw [hαcard, hTcard]; exact hr3)
    have hdegα : ∀ θ ∈ ({α₁, α₂, α₃} : Finset basis.index),
        (Module.finrank ℂ (basis.representation θ).vector : ℤ) = D := by
      intro θ hθ
      rw [← hTeq] at hθ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hθ
      exact hdegZ i hi
    have h1 := hdegα α₁ (by simp)
    have h2 := hdegα α₂ (by simp)
    have h3 := hdegα α₃ (by simp)
    rw [h1, h2, h3] at hrel
    have hdvd : D ∣ 1 := ⟨-(ε₁ + ε₂ + ε₃), by linear_combination hrel⟩
    have hD1 : 1 < D := by
      rw [← h1]
      exact_mod_cast hf₁
    have := Int.le_of_dvd one_pos hdvd
    omega
  have hFodd : Odd (Module.finrank ℂ (basis.representation χ).vector) := by
    have hδodd : Odd δ := by rcases hδ with rfl | rfl <;> decide
    have h := heven.sub_odd hδodd
    rw [add_sub_cancel_right] at h
    exact Int.odd_coe_nat _ |>.mp h
  have hχα := hmemα χ hχp (hreal χ hχB) hFodd
  have hF1 : 1 < Module.finrank ℂ (basis.representation χ).vector := by
    rcases hχα with h | h | h <;> rw [h] <;> assumption
  refine ⟨δ, χ, ψ, hδ, hχp, hψne, hψinj, hB, hreal, hχα, hF1, hFodd, fun i hi => ?_, hreg, hvals,
    hconj, hsum⟩
  have h := hdegZ i hi
  refine ⟨h, ?_, ?_⟩
  · have := hpos
    omega
  · rw [← Int.even_coe_nat, h]
    exact heven

end Core

section Node

variable {G : Type} [Group G] [Fintype G]

theorem prime_inversion_family_odd_member_from_three_odd_principal_two_characters
    (basis : FiniteIrreducibleCharacterBasis G) (ideal₂ : Ideal ComplexAlgebraicIntegers)
    [ideal₂.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (α₁ α₂ α₃ : basis.index) (hnodup : [principal, α₁, α₂, α₃].Nodup)
    (hodd₂ : ∀ θ, (θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal ∧
        Odd (Module.finrank ℂ (basis.representation θ).vector)) ↔
      θ = principal ∨ θ = α₁ ∨ θ = α₂ ∨ θ = α₃)
    (hf₁ : 1 < Module.finrank ℂ (basis.representation α₁).vector)
    (hf₂ : 1 < Module.finrank ℂ (basis.representation α₂).vector)
    (hf₃ : 1 < Module.finrank ℂ (basis.representation α₃).vector)
    (ε₁ ε₂ ε₃ : ℤ)
    (hrel : 1 + ε₁ * (Module.finrank ℂ (basis.representation α₁).vector : ℤ) +
      ε₂ * (Module.finrank ℂ (basis.representation α₂).vector : ℤ) +
      ε₃ * (Module.finrank ℂ (basis.representation α₃).vector : ℤ) = 0)
    (idealℓ : Ideal ComplexAlgebraicIntegers) [idealℓ.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ idealℓ) ℓ] (hℓ : 7 ≤ ℓ) (P : Sylow ℓ G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 2) :
    ∃ (δ : ℤ) (χ : basis.index) (ψ : ℕ → basis.index),
      (δ = 1 ∨ δ = -1) ∧ χ ≠ principal ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ψ i ≠ principal ∧ ψ i ≠ χ) ∧
      Set.InjOn ψ (Finset.Icc 1 ((ℓ - 1) / 2)) ∧
      coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal =
        insert principal (insert χ ((Finset.Icc 1 ((ℓ - 1) / 2)).image ψ)) ∧
      (∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal, ∀ g : G,
        starRingEnd ℂ ((basis.representation θ).character g) =
          (basis.representation θ).character g) ∧
      (χ = α₁ ∨ χ = α₂ ∨ χ = α₃) ∧
      1 < Module.finrank ℂ (basis.representation χ).vector ∧
      Odd (Module.finrank ℂ (basis.representation χ).vector) ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2),
        (Module.finrank ℂ (basis.representation (ψ i)).vector : ℤ) =
          (Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ ∧
        0 < Module.finrank ℂ (basis.representation (ψ i)).vector ∧
        Even (Module.finrank ℂ (basis.representation (ψ i)).vector)) ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ∀ x : G, ¬ ℓ ∣ orderOf x →
        (basis.representation (ψ i)).character x = (basis.representation χ).character x + δ) ∧
      (∀ j ∈ Finset.Icc 1 (ℓ - 1), ∀ y ∈ Subgroup.centralizer (P : Set G), ¬ ℓ ∣ orderOf y →
        (basis.representation χ).character (u ^ j * y) = δ ∧
        ∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2),
          (basis.representation (ψ i)).character (u ^ j * y) =
            δ * (Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ ((i * j : ℕ) : ℤ) +
              Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ (-((i * j : ℕ) : ℤ)))) ∧
      (∀ z : G, ℓ ∣ orderOf z → ∃ j ∈ Finset.Icc 1 (ℓ - 1),
        ∃ y ∈ Subgroup.centralizer (P : Set G), ¬ ℓ ∣ orderOf y ∧ IsConj z (u ^ j * y)) ∧
      ∀ x₁ x₂ z : G, ¬ ℓ ∣ orderOf x₁ → ¬ ℓ ∣ orderOf x₂ → ℓ ∣ orderOf z →
        ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal,
          (basis.representation θ).character x₁ * (basis.representation θ).character x₂ *
            (basis.representation θ).character z / (basis.representation θ).character 1 =
          ((basis.representation χ).character 1 - (basis.representation χ).character x₁) *
            ((basis.representation χ).character 1 - (basis.representation χ).character x₂) /
              ((basis.representation χ).character 1 *
                ((basis.representation χ).character 1 + δ)) :=
  prime_inversion_family_odd_member_of_real_odd_principal basis ideal₂ principal hprincipal
    α₁ α₂ α₃ hnodup hodd₂ hf₁ hf₂ hf₃ ε₁ ε₂ ε₃ hrel
    (fun θ hθr hθo => real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal₂
      principal hprincipal θ hθr hθo)
    idealℓ ℓ hℓ P u hPu hP hindex

end Node

end CFSG.Semidihedral.Principal
