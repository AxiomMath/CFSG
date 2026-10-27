module

public import CFSG.CharacterTheory.Semidihedral.Principal.SpectrumRestrictionRigiditySupport
public import CFSG.CharacterTheory.Semidihedral.Principal.UnitarySignSpectrumBound

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal.SpectrumRigidity

universe u w₁ w₂ w₃

variable {H : Type u} [Group H] [Fintype H]

theorem regular_principal_spectrum_restriction_rigidity
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (t : H) (ht : orderOf t = 2)
    (q k : ℕ) (hq : 5 ≤ q) (hk : 2 ≤ k) (e : ℤ) (he : e = 1 ∨ e = -1)
    (α₁ α₂ α₃ α₄ : basis.index) (Ψ : Fin (k - 1) → basis.index) (N : Fin k → basis.index)
    (hB : ∀ c, c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      c = principal ∨ c = α₁ ∨ c = α₂ ∨ c = α₃ ∨ c = α₄ ∨ (∃ j, c = Ψ j) ∨ ∃ l, c = N l)
    (hdistinct : Function.Injective (Sum.elim ![principal, α₁, α₂, α₃, α₄] (Sum.elim Ψ N)))
    (hα₁ : (Module.finrank ℂ (basis.representation α₁).vector : ℤ) = q ^ 3)
    (hα₂ : (Module.finrank ℂ (basis.representation α₂).vector : ℤ) = q ^ 2 - e * q + 1)
    (hα₃ : (Module.finrank ℂ (basis.representation α₃).vector : ℤ) = q * (q ^ 2 - e * q + 1))
    (hα₄ : (Module.finrank ℂ (basis.representation α₄).vector : ℤ) = q ^ 2 - e * q)
    (hΨ : ∀ j, (Module.finrank ℂ (basis.representation (Ψ j)).vector : ℤ) = q ^ 3 + e)
    (hN : ∀ l, (Module.finrank ℂ (basis.representation (N l)).vector : ℤ) = q ^ 3 + e)
    (hα₂t : (basis.representation α₂).character t = e * q)
    (hα₄t : (basis.representation α₄).character t = 1 - e * q)
    (θ₁ : FiniteComplexRepresentation.{u, w₁} H) (θ₂ : FiniteComplexRepresentation.{u, w₂} H)
    (θ₃ : FiniteComplexRepresentation.{u, w₃} H) (hf₁ : 1 < Module.finrank ℂ θ₁.vector)
    (hf₂ : 1 < Module.finrank ℂ θ₂.vector) (_hf₃ : 1 < Module.finrank ℂ θ₃.vector)
    (δ₁ δ₂ δ₃ : ℤ)
    (hδ : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hsum : 1 + δ₁ * (Module.finrank ℂ θ₁.vector : ℤ) + δ₂ * (Module.finrank ℂ θ₂.vector : ℤ) +
      δ₃ * (Module.finrank ℂ θ₃.vector : ℤ) = 0)
    (hprod : Module.finrank ℂ θ₁.vector * Module.finrank ℂ θ₂.vector =
      q ^ 2 * Module.finrank ℂ θ₃.vector) :
    let χ : basis.index → H → ℂ := fun c => (basis.representation c).character
    let T : H → ℂ := χ principal + (e : ℂ) • χ α₁ - χ α₂ - (e : ℂ) • χ α₃
    let E : Fin (k - 1) → H → ℂ := fun j => χ principal + (e : ℂ) • χ α₁ - (e : ℂ) • χ (Ψ j)
    let F : Fin k → H → ℂ := fun l => χ (N l) - χ (N ⟨0, by omega⟩)
    let U : H → ℂ := χ principal - (e : ℂ) • χ α₁ - χ α₂ + (e : ℂ) • χ α₃ + (2 : ℂ) • χ α₄
    let V : H → ℂ := (e : ℂ) • χ α₁ + χ α₂ - χ α₄ + (e : ℂ) • ∑ j, χ (Ψ j) -
      (e : ℂ) • ∑ l, χ (N l)
    characterPairing θ₁.character T = δ₁ → characterPairing θ₂.character T = δ₂ →
    characterPairing θ₃.character T = δ₃ →
    (∀ j, characterPairing θ₁.character (E j) = δ₁) →
    (∀ l : Fin k, 1 ≤ (l : ℕ) → characterPairing θ₁.character (F l) = 0) →
    characterPairing θ₁.character U = -δ₁ → characterPairing θ₁.character V = δ₁ →
    (δ₂ = -1 → ∀ u : H, 2 ∣ orderOf u → θ₂.character u = χ α₂ u) →
    θ₂.character = χ α₂ ∧ δ₁ = e ∧ δ₂ = -1 ∧ δ₃ = -e ∧
      (Module.finrank ℂ θ₁.vector : ℤ) = q ^ 3 ∧
      (Module.finrank ℂ θ₂.vector : ℤ) = q ^ 2 - e * q + 1 ∧
      (Module.finrank ℂ θ₃.vector : ℤ) = q * (q ^ 2 - e * q + 1) := by
  intro χ T E F U V hT₁ hT₂ _hT₃ hE hF hU hV hEven
  have hq2 : 2 ≤ q := by omega
  have hqZ : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hq1Z : (1 : ℤ) ≤ q := by omega
  have hq2Z : (2 : ℤ) ≤ q := by omega
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have hprodZ : (Module.finrank ℂ θ₁.vector : ℤ) * Module.finrank ℂ θ₂.vector =
      (q : ℤ) ^ 2 * Module.finrank ℂ θ₃.vector := by exact_mod_cast hprod
  obtain ⟨a, ha, hf₁sum⟩ := exists_multiplicity basis θ₁
  obtain ⟨m, hm, hf₂sum⟩ := exists_multiplicity basis θ₂
  have hT₁' : (a principal : ℤ) + e * a α₁ - a α₂ - e * a α₃ = δ₁ := by
    have h := hT₁
    simp only [T, χ, pairing_add_right, pairing_sub_right, pairing_smul_right, ha] at h
    exact_mod_cast h
  have hT₂' : (m principal : ℤ) + e * m α₁ - m α₂ - e * m α₃ = δ₂ := by
    have h := hT₂
    simp only [T, χ, pairing_add_right, pairing_sub_right, pairing_smul_right, hm] at h
    exact_mod_cast h
  have hE' : ∀ j, (a principal : ℤ) + e * a α₁ - e * a (Ψ j) = δ₁ := by
    intro j
    have h := hE j
    simp only [E, χ, pairing_add_right, pairing_sub_right, pairing_smul_right, ha] at h
    exact_mod_cast h
  have hF' : ∀ l : Fin k, a (N l) = a (N ⟨0, by omega⟩) := by
    intro l
    by_cases hl : 1 ≤ (l : ℕ)
    · have h := hF l hl
      simp only [F, χ, pairing_sub_right, ha] at h
      have h' : ((a (N l) : ℕ) : ℂ) = ((a (N ⟨0, by omega⟩) : ℕ) : ℂ) := by
        linear_combination h
      exact_mod_cast h'
    · rw [show l = ⟨0, by omega⟩ from Fin.ext (show (l : ℕ) = 0 by omega)]
  have hU' : (a principal : ℤ) - e * a α₁ - a α₂ + e * a α₃ + 2 * a α₄ = -δ₁ := by
    have h := hU
    simp only [U, χ, pairing_add_right, pairing_sub_right, pairing_smul_right, ha] at h
    exact_mod_cast h
  have hV' : e * (a α₁ : ℤ) + a α₂ - a α₄ + e * ∑ j, (a (Ψ j) : ℤ) -
      e * ∑ l, (a (N l) : ℤ) = δ₁ := by
    have h := hV
    simp only [V, χ, pairing_add_right, pairing_sub_right, pairing_smul_right,
      pairing_sum_right, ha] at h
    exact_mod_cast h
  have hlow₁ : ∀ c, 1 ≤ a c →
      (Module.finrank ℂ (basis.representation c).vector : ℤ) ≤ Module.finrank ℂ θ₁.vector :=
    fun c hc => by exact_mod_cast degree_le_of_mem basis a hf₁sum c hc
  have hlow₂ : ∀ c, 1 ≤ m c →
      (Module.finrank ℂ (basis.representation c).vector : ℤ) ≤ Module.finrank ℂ θ₂.vector :=
    fun c hc => by exact_mod_cast degree_le_of_mem basis m hf₂sum c hc
  have hj₀ : 0 < k - 1 := by omega
  have hf₁Z : (1 : ℤ) < Module.finrank ℂ θ₁.vector := by exact_mod_cast hf₁
  have hf₂Z : (1 : ℤ) < Module.finrank ℂ θ₂.vector := by exact_mod_cast hf₂
  have hsqcube := sq_le_cube hq1Z
  rcases he with rfl | rfl
  ·
    have hd₂ : (Module.finrank ℂ (basis.representation α₂).vector : ℤ) = q ^ 2 - q + 1 := by
      rw [hα₂]; ring
    have hd₃ : (Module.finrank ℂ (basis.representation α₃).vector : ℤ) =
        q * (q ^ 2 - q + 1) := by rw [hα₃]; ring
    have hd₄ : (Module.finrank ℂ (basis.representation α₄).vector : ℤ) = q ^ 2 - q := by
      rw [hα₄]; ring
    have hδ' : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1) := by
      rcases hδ with h | ⟨rfl, rfl, rfl⟩ | h
      · exact Or.inl h
      · exfalso
        have hlt := lt_sq_of_second_positive hq1Z hf₁Z (by omega) hsum hprodZ
        have hmem : 1 ≤ a (Ψ ⟨0, hj₀⟩) := by have := hE' ⟨0, hj₀⟩; omega
        have := hlow₁ _ hmem
        rw [hΨ] at this
        linarith
      · exact Or.inr h
    have hδ₂ : δ₂ = -1 := by rcases hδ' with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> exact h
    have hbound : 3 * (Module.finrank ℂ θ₂.vector : ℤ) < 3 * q ^ 2 + q ∧
        (δ₁ = -1 → (q : ℤ) ^ 2 < Module.finrank ℂ θ₂.vector) := by
      rcases hδ' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      ·
        have hΨb : ∀ j, (a (Ψ j) : ℤ) = a principal + a α₁ + 1 := fun j => by
          have := hE' j
          linarith
        have hc : ∀ l, (a (N l) : ℤ) = a (N ⟨0, by omega⟩) := fun l => by
          exact_mod_cast hF' l
        have hsumΨ : ∑ j, (a (Ψ j) : ℤ) = ((k : ℤ) - 1) * (a principal + a α₁ + 1) := by
          rw [Finset.sum_congr rfl fun j _ => hΨb j, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ k)]
          simp
        have hsumN : ∑ l, (a (N l) : ℤ) = (k : ℤ) * a (N ⟨0, by omega⟩) := by
          rw [Finset.sum_congr rfl fun l _ => hc l, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
        rw [hsumΨ, hsumN] at hV'
        have hkb : 2 * ((k : ℤ) * (a (N ⟨0, by omega⟩) - (a principal + a α₁ + 1))) = 0 := by
          linear_combination -2 * hV' - hT₁' - hU'
        have hkz : (2 : ℤ) * k ≠ 0 := by omega
        have hcb : (a (N ⟨0, by omega⟩) : ℤ) = a principal + a α₁ + 1 := by
          rw [← mul_assoc] at hkb
          have := (mul_eq_zero.mp hkb).resolve_left hkz
          linarith
        have hNb : ∀ l, (a (N l) : ℤ) = a principal + a α₁ + 1 := fun l => by rw [hc l, hcb]
        have h23 : (a α₂ : ℤ) + a α₃ = a principal + a α₁ + 1 := by linarith
        have h24 : (a α₂ : ℤ) = a principal + a α₄ := by linarith
        have hf₁big := exceptional_lower_bound basis hq hk a hf₁sum principal α₁ α₂ α₃ α₄ Ψ N
          hdistinct hd₂ hd₃ hd₄ hΨ hN hΨb hNb h23 h24
        have hex := excess_product_of_third_positive hsum hprodZ
        have := small_excess_of_large hqZ hf₁big hex
        exact ⟨this.2, fun _ => this.1⟩
      · have := (lt_sq_of_first_positive hq1Z (by omega) hf₂Z hsum hprodZ).2
        exact ⟨by linarith, fun h => by norm_num at h⟩
    have hm₂ : 1 ≤ m α₂ := by
      have h := hT₂'
      rw [hδ₂] at h
      by_contra hlt
      have hm₃ : 1 ≤ m α₃ := by omega
      have := hlow₂ _ hm₃
      rw [hd₃] at this
      linarith [hbound.1, three_sq_lt_gap hqZ]
    obtain ⟨Ξ, hΞchar, hΞdeg⟩ := exists_remove_constituent basis θ₂ m hm hf₂sum α₂ hm₂
    have hΞvan : ∀ x : H, 2 ∣ orderOf x → Ξ.character x = 0 := by
      intro x hx
      rw [hΞchar, Pi.sub_apply, hEven hδ₂ x hx, sub_self]
    have hΞsmall : 3 * (Module.finrank ℂ Ξ.vector : ℤ) < 4 * q := by
      have : (Module.finrank ℂ Ξ.vector : ℤ) +
          Module.finrank ℂ (basis.representation α₂).vector = Module.finrank ℂ θ₂.vector := by
        exact_mod_cast hΞdeg
      rw [hd₂] at this
      linarith [hbound.1]
    have hΞzero : Ξ.character = 0 := by
      by_contra hne
      have hα₂B : α₂ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
        (hB α₂).mpr (Or.inr (Or.inr (Or.inl rfl)))
      have hα₄B : α₄ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
        (hB α₄).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have hne₂₄ : α₂ ≠ α₄ := by
        have := hdistinct.ne (Sum.inl_injective.ne (show (2 : Fin 5) ≠ 4 by decide))
        simpa using this
      have hne₂₀ : α₂ ≠ principal := by
        have := hdistinct.ne (Sum.inl_injective.ne (show (2 : Fin 5) ≠ 0 by decide))
        simpa using this
      have hne₄₀ : α₄ ≠ principal := by
        have := hdistinct.ne (Sum.inl_injective.ne (show (4 : Fin 5) ≠ 0 by decide))
        simpa using this
      have hα₂N : Module.finrank ℂ (basis.representation α₂).vector = q ^ 2 - q + 1 := by
        zify [hqq]
        linarith
      have hα₄N : Module.finrank ℂ (basis.representation α₄).vector = q ^ 2 - q := by
        zify [hqq]
        linarith
      have hα₂t' : (basis.representation α₂).character t = q := by
        rw [hα₂t]
        push_cast
        ring
      have hα₄t' : (basis.representation α₄).character t = 1 - q := by
        rw [hα₄t]
        push_cast
        ring
      have hgap : ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          c ≠ principal → c ≠ α₂ → c ≠ α₄ →
            q * (q ^ 2 - q + 1) ≤ Module.finrank ℂ (basis.representation c).vector := by
        intro c hc h0 h2 h4
        zify [hqq]
        have hgc := gap_le_cube hq1Z
        rcases (hB c).mp hc with h | h | h | h | h | ⟨j, h⟩ | ⟨l, h⟩
        · exact absurd h h0
        · rw [h, hα₁]
          exact hgc
        · exact absurd h h2
        · rw [h, hd₃]
        · exact absurd h h4
        · rw [h, hΨ j]
          linarith
        · rw [h, hN l]
          linarith
      have hbig := (regular_unitary_sign_principal_spectrum_vanishing_bound basis ideal principal
        hprincipal t ht q hq α₂ α₄ hα₂B hα₄B hne₂₄ hne₂₀ hne₄₀ hα₂N hα₄N hα₂t' hα₄t' hgap Ξ hne
        hΞvan).2
      have hsmallR : 3 * (Module.finrank ℂ Ξ.vector : ℝ) < 4 * q := by exact_mod_cast hΞsmall
      linarith
    have hθ₂ : θ₂.character = χ α₂ := by
      have h := hΞchar
      rw [hΞzero] at h
      exact (sub_eq_zero.mp h.symm)
    have hf₂eq : (Module.finrank ℂ θ₂.vector : ℤ) = q ^ 2 - q + 1 := by
      have h := congrFun hθ₂ 1
      simp only [χ, FiniteComplexRepresentation.character, Representation.char_one] at h
      rw [← hd₂]
      exact_mod_cast h
    have hδ₁ : δ₁ = 1 ∧ δ₃ = -1 := by
      rcases hδ' with ⟨rfl, -, -⟩ | ⟨h1, -, h3⟩
      · exfalso
        have := hbound.2 rfl
        linarith
      · exact ⟨h1, h3⟩
    obtain ⟨rfl, rfl⟩ := hδ₁
    rw [hδ₂] at hsum
    obtain ⟨hO1, -⟩ := lt_sq_of_first_positive hq1Z (by omega) hf₂Z hsum hprodZ
    rw [hf₂eq] at hO1
    have hf₁eq : (Module.finrank ℂ θ₁.vector : ℤ) = q ^ 3 := by
      have hq1 : (1 : ℤ) - q ≠ 0 := by omega
      have h' : (Module.finrank ℂ θ₁.vector : ℤ) * (1 - q) = q ^ 3 * (1 - q) := by
        linear_combination hO1
      exact mul_right_cancel₀ hq1 h'
    refine ⟨hθ₂, rfl, hδ₂, by norm_num, hf₁eq, by rw [hf₂eq]; ring, ?_⟩
    linear_combination -hsum + hf₁eq - hf₂eq
  ·
    have hd₂ : (Module.finrank ℂ (basis.representation α₂).vector : ℤ) = q ^ 2 + q + 1 := by
      rw [hα₂]; ring
    have hcube := sq_add_lt_cube hq2Z
    have hδ₁₂ : δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1 := by
      rcases hδ with h | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact h
      · exfalso
        have hlt := lt_sq_of_second_positive hq1Z hf₁Z (by omega) hsum hprodZ
        have h12 : 1 ≤ a α₁ ∨ 1 ≤ a α₂ := by omega
        rcases h12 with h | h
        · have := hlow₁ _ h
          rw [hα₁] at this
          linarith
        · have := hlow₁ _ h
          rw [hd₂] at this
          linarith
      · exfalso
        have hlt := (lt_sq_of_first_positive hq1Z (by omega) hf₂Z hsum hprodZ).2
        have h12 : 1 ≤ m α₁ ∨ 1 ≤ m α₂ := by omega
        rcases h12 with h | h
        · have := hlow₂ _ h
          rw [hα₁] at this
          linarith
        · have := hlow₂ _ h
          rw [hd₂] at this
          linarith
    obtain ⟨rfl, rfl, rfl⟩ := hδ₁₂
    have ha₁ : 1 ≤ a α₁ := by
      have := hE' ⟨0, hj₀⟩
      omega
    have hf₁big : (q : ℤ) ^ 3 ≤ Module.finrank ℂ θ₁.vector := by
      have := hlow₁ _ ha₁
      rwa [hα₁] at this
    have hex := excess_product_of_third_positive hsum hprodZ
    obtain ⟨-, hf₂le⟩ := excess_le_of_cube_le hq2Z hf₁big hex
    have hm₂ : 1 ≤ m α₂ := by
      by_contra hlt
      have hm₁ : 1 ≤ m α₁ := by omega
      have := hlow₂ _ hm₁
      rw [hα₁] at this
      linarith
    have hθ₂ : θ₂.character = χ α₂ :=
      character_eq_of_degree_le basis θ₂ m hm hf₂sum α₂ hm₂ (by
        zify
        linarith)
    have hf₂eq : (Module.finrank ℂ θ₂.vector : ℤ) = q ^ 2 + q + 1 := by
      have := hlow₂ _ hm₂
      linarith
    have hf₁eq : (Module.finrank ℂ θ₁.vector : ℤ) = q ^ 3 := by
      rw [hf₂eq] at hex
      exact eq_cube_of_excess hq2Z (by linear_combination hex)
    refine ⟨hθ₂, rfl, rfl, by norm_num, hf₁eq, by rw [hf₂eq]; ring, ?_⟩
    linear_combination hsum + hf₁eq + hf₂eq

end CFSG.Semidihedral.Principal
