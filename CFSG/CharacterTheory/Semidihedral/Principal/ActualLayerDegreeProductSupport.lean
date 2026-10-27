module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualSimpleLayerExhaustionSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.NonsimpleFourierOddDegreeProduct

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

@[expose] def ActualPrincipalDegreeRelations {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (q : ℕ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) : Prop :=
  1 < Module.finrank ℂ (basis.representation χ₁).vector ∧
  1 < Module.finrank ℂ (basis.representation χ₂).vector ∧
  1 < Module.finrank ℂ (basis.representation χ₃).vector ∧
  1 < Module.finrank ℂ (basis.representation χ₄).vector ∧
  ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
    (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧
  δ₄ = -δ₂ ∧
  (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) =
    Module.finrank ℂ (basis.representation χ₂).vector + δ₂ ∧
  Module.finrank ℂ (basis.representation χ₁).vector *
      Module.finrank ℂ (basis.representation χ₂).vector =
    q ^ 2 * Module.finrank ℂ (basis.representation χ₃).vector ∧
  (1 : ℚ) + δ₁ * q ^ 2 / Module.finrank ℂ (basis.representation χ₁).vector +
      δ₂ * q ^ 2 / Module.finrank ℂ (basis.representation χ₂).vector +
      δ₃ / Module.finrank ℂ (basis.representation χ₃).vector = 0

theorem sign_relation_of_degree_identity {δ₂ δ₄ : ℤ} (hδ₂ : δ₂ = 1 ∨ δ₂ = -1)
    (hδ₄ : δ₄ = 1 ∨ δ₄ = -1) {f₂ f₄ : ℤ} (hf₂ : 1 < f₂) (hf₄ : 1 < f₄)
    (h : 1 + δ₂ * f₂ + δ₄ * f₄ = 0) : δ₄ = -δ₂ ∧ f₄ = f₂ + δ₂ := by
  rcases hδ₂ with rfl | rfl <;> rcases hδ₄ with rfl | rfl <;> constructor <;> linarith

theorem actual_principal_degree_relations_of_family {G : Type} [Group G] [Fintype G]
    (hindex : ∀ H : Subgroup G, H.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1) (k : ℕ)
    (φ : C t → ℂ) (hφ1 : φ 1 = q) (hφnc : ∃ y : C t, Odd (orderOf y) ∧ φ y ≠ q)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e k φ
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ := by
  obtain ⟨-, hδ₁, hδ₂, hδ₃, hδ₄, hnd, -, -, -, -, -, hB, -, hodd, hsec, hrel⟩ := hfam
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hBdef
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₁B : χ₁ ∈ B := hmem χ₁ (by simp)
  have hχ₂B : χ₂ ∈ B := hmem χ₂ (by simp)
  have hχ₃B : χ₃ ∈ B := hmem χ₃ (by simp)
  have hχ₄B : χ₄ ∈ B := hmem χ₄ (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, -⟩ := hnd
  set f₁ := Module.finrank ℂ (basis.representation χ₁).vector with hf₁def
  set f₂ := Module.finrank ℂ (basis.representation χ₂).vector with hf₂def
  set f₃ := Module.finrank ℂ (basis.representation χ₃).vector with hf₃def
  set f₄ := Module.finrank ℂ (basis.representation χ₄).vector with hf₄def
  have hf₁ : (basis.representation χ₁).character 1 = f₁ := (basis_character_one basis χ₁).1
  have hf₂ : (basis.representation χ₂).character 1 = f₂ := (basis_character_one basis χ₂).1
  have hf₃ : (basis.representation χ₃).character 1 = f₃ := (basis_character_one basis χ₃).1
  have hf₄ : (basis.representation χ₄).character 1 = f₄ := (basis_character_one basis χ₄).1
  have hoddF : ∀ c ∈ B, (∃ d : ℕ, Odd d ∧ (basis.representation c).character 1 = d) ↔
      (c = principal ∨ c = χ₁ ∨ c = χ₂ ∨ c = χ₃) := by
    intro c hc
    rw [← hodd c hc, (basis_character_one basis c).1]
    constructor
    · rintro ⟨d, hd, hcd⟩
      rwa [Nat.cast_injective hcd]
    · intro h
      exact ⟨_, h, rfl⟩
  let Φ : G → ℂ := fun g => if h : g ∈ C t then φ ⟨g, h⟩ else 0
  have hΦC : ∀ (y : G) (hy : y ∈ C t), Φ y = φ ⟨y, hy⟩ := fun y hy => by
    simp only [Φ, hy, dite_true]
  have hΦ1 : Φ 1 = q := by
    rw [hΦC 1 (one_mem _)]
    exact hφ1
  have hΦ : ∃ y₁ ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      ∃ y₂ ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
        Odd (orderOf y₁) ∧ Odd (orderOf y₂) ∧ Φ y₁ ≠ Φ y₂ := by
    rw [hcent]
    obtain ⟨y, hy, hyq⟩ := hφnc
    refine ⟨1, one_mem _, y, y.2, by simp, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact hy
    · rw [hΦ1, hΦC y y.2]
      exact fun h => hyq h.symm
  have hχ₁t : ∀ y ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      Odd (orderOf y) →
      (basis.representation χ₁).character ((e' (r n) : G) ^ (modulus n / 2) * y) =
        δ₁ * e * Φ y := by
    rw [hcent]
    intro y hy hyo
    rw [hΦC y hy]
    exact (hsec ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk]; exact hyo)).1
  have hχ₂t : ∀ y ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      Odd (orderOf y) →
      (basis.representation χ₂).character ((e' (r n) : G) ^ (modulus n / 2) * y) =
        -δ₂ * e * Φ y := by
    rw [hcent]
    intro y hy hyo
    rw [hΦC y hy, (hsec ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk]; exact hyo)).2.1]
    ring
  have hχ₃t : ∀ y ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      Odd (orderOf y) →
      (basis.representation χ₃).character ((e' (r n) : G) ^ (modulus n / 2) * y) = -δ₃ := by
    rw [hcent]
    intro y hy hyo
    exact (hsec ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk]; exact hyo)).2.2.1
  obtain ⟨-, -, hrel1, hrel2⟩ := hrel 1 (by simp)
  rw [hf₁, hf₂, hf₃] at hrel1
  rw [hf₂, hf₄] at hrel2
  have hdeg : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0 := by
    exact_mod_cast hrel1
  have hdeg₄ : 1 + δ₂ * (f₂ : ℤ) + δ₄ * f₄ = 0 := by
    exact_mod_cast hrel2
  obtain ⟨-, -, hf₁1, hf₂1, hf₃1, hsign, hrec, hprod⟩ :=
    nonsimple_principal_Fourier_odd_degree_product hindex hn e' basis ideal principal hprincipal
      χ₁ χ₂ χ₃ hχ₁B hχ₂B hχ₃B h01 h02 h03 h12 h13 h23 hoddF f₁ f₂ f₃ hf₁ hf₂ hf₃ q hq3 hqodd e
      δ₁ δ₂ δ₃ he hδ₁ hδ₂ hδ₃ Φ hΦ hΦ1 hχ₁t hχ₂t hχ₃t hdeg
  have hf₄even : ¬ Odd f₄ := fun h => by
    rcases (hodd χ₄ hχ₄B).mp h with h | h | h | h
    · exact h04 h.symm
    · exact h14 h.symm
    · exact h24 h.symm
    · exact h34 h.symm
  have hf₄pos : 0 < f₄ := (basis_character_one basis χ₄).2
  have hf₄1 : 1 < f₄ := by
    rcases Nat.even_or_odd f₄ with h | h
    · obtain ⟨m, hm⟩ := h
      omega
    · exact absurd h hf₄even
  obtain ⟨hδ₄₂, hf₄₂⟩ := sign_relation_of_degree_identity hδ₂ hδ₄ (by exact_mod_cast hf₂1)
    (by exact_mod_cast hf₄1) hdeg₄
  exact ⟨hf₁1, hf₂1, hf₃1, hf₄1, hsign, hδ₄₂, hf₄₂, hprod, hrec⟩

end CFSG.Semidihedral.Principal
