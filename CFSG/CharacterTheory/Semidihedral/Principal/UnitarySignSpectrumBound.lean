module

public import CFSG.CharacterTheory.Semidihedral.Principal.TensorGapBound

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u w

theorem unitary_sign_multiplicity_bound {q a c : ℤ} (hq : 5 ≤ q) (ha : 0 ≤ a)
    (h : 1 + a * q = c * (q - 1)) :
    q * (q ^ 2 - q + 1) ≤ 1 + a * (q ^ 2 - q + 1) + c * (q ^ 2 - q) := by
  have hfac : 1 + a = (c - a) * (q - 1) := by linear_combination h
  have hca : 1 ≤ c - a := by
    by_contra hlt
    have hle : c - a ≤ 0 := by omega
    have : (c - a) * (q - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle (by omega)
    omega
  have ha2 : q - 2 ≤ a := by
    have : (q - 1) ≤ (c - a) * (q - 1) := by nlinarith
    omega
  have hc1 : q - 1 ≤ c := by nlinarith
  have hb : 0 ≤ q ^ 2 - q + 1 := by nlinarith
  have hb' : 0 ≤ q ^ 2 - q := by nlinarith
  have h1 : (q - 2) * (q ^ 2 - q + 1) ≤ a * (q ^ 2 - q + 1) := mul_le_mul_of_nonneg_right ha2 hb
  have h2 : (q - 1) * (q ^ 2 - q) ≤ c * (q ^ 2 - q) := mul_le_mul_of_nonneg_right hc1 hb'
  have h3 : 0 ≤ (q - 5) * q ^ 2 := mul_nonneg (by omega) (sq_nonneg q)
  nlinarith

variable {H : Type u} [Group H] [Fintype H]

theorem regular_unitary_sign_principal_spectrum_vanishing_bound
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (t : H) (ht : orderOf t = 2)
    (q : ℕ) (hq : 5 ≤ q) (α β : basis.index)
    (_hαB : α ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (_hβB : β ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hαβ : α ≠ β) (hαp : α ≠ principal) (hβp : β ≠ principal)
    (hα1 : Module.finrank ℂ (basis.representation α).vector = q ^ 2 - q + 1)
    (hβ1 : Module.finrank ℂ (basis.representation β).vector = q ^ 2 - q)
    (hαt : (basis.representation α).character t = q)
    (hβt : (basis.representation β).character t = 1 - q)
    (hgap : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      χ ≠ principal → χ ≠ α → χ ≠ β →
        q * (q ^ 2 - q + 1) ≤ Module.finrank ℂ (basis.representation χ).vector)
    (Θ : FiniteComplexRepresentation.{u, w} H) (hΘ : Θ.character ≠ 0)
    (hΘvan : ∀ x : H, 2 ∣ orderOf x → Θ.character x = 0) :
    4 * ((q : ℝ) ^ 2 - q) ≤ (Module.finrank ℂ Θ.vector : ℝ) ^ 2 ∧
      4 * (q : ℝ) / 3 ≤ (Module.finrank ℂ Θ.vector : ℝ) := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set deg : basis.index → ℕ := fun χ => Module.finrank ℂ (basis.representation χ).vector
    with hdeg
  have hq1 : 1 ≤ q := by omega
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hdegp : deg principal = 1 := by
    have e := congrFun hprincipal 1
    rw [Pi.one_apply] at e
    change (basis.representation principal).representation.character 1 = 1 at e
    rw [Representation.char_one] at e
    exact_mod_cast e
  have hdegB : ∀ χ ∈ B, χ ≠ principal →
      ((q : ℝ) ^ 2 - q) ≤ (Module.finrank ℂ (basis.representation χ).vector : ℝ) := by
    intro χ hχ hχp
    have hcast : ((q ^ 2 - q : ℕ) : ℝ) = (q : ℝ) ^ 2 - q := by
      rw [Nat.cast_sub hqq]
      push_cast
      ring
    by_cases h1 : χ = α
    · rw [h1, hα1, ← hcast]
      exact_mod_cast Nat.le_succ _
    by_cases h2 : χ = β
    · rw [h2, hβ1, ← hcast]
    · have h3 := hgap χ hχ hχp h1 h2
      rw [← hcast]
      have : q ^ 2 - q ≤ q * (q ^ 2 - q + 1) := by nlinarith
      exact_mod_cast this.trans h3
  have hΞ : ∀ Ξ : FiniteComplexRepresentation.{u, u} H,
      (∀ χ, χ ∉ B → characterPairing Ξ.character (basis.representation χ).character = 0) →
      characterPairing Ξ.character (basis.representation principal).character = 1 →
      (∀ x : H, 2 ∣ orderOf x → Ξ.character x = 0) →
      ((q : ℝ) * (q ^ 2 - q + 1)) ≤ (Module.finrank ℂ Ξ.vector : ℝ) := by
    intro Ξ hsupp hprin hvan
    choose m hm using characterPairing_basis_natural basis Ξ
    have hfin := finrank_eq_sum_multiplicity basis Ξ m (fun χ => (hm χ).symm)
    have hm0 : ∀ χ, χ ∉ B → m χ = 0 := fun χ hχ => by
      have e := hsupp χ hχ
      rw [hm χ] at e
      exact_mod_cast e
    have hm1 : m principal = 1 := by
      have e := hprin
      rw [hm principal] at e
      exact_mod_cast e
    have hterm : ∀ χ, m χ * deg χ ≤ Module.finrank ℂ Ξ.vector := fun χ => by
      rw [hfin]
      exact Finset.single_le_sum (f := fun ψ => m ψ * deg ψ) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ χ)
    by_contra hlt
    replace hlt := not_le.mp hlt
    have hltN : Module.finrank ℂ Ξ.vector < q * (q ^ 2 - q + 1) := by
      have hcast : ((q * (q ^ 2 - q + 1) : ℕ) : ℝ) = (q : ℝ) * (q ^ 2 - q + 1) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hqq]
        push_cast
        ring
      rw [← hcast] at hlt
      exact_mod_cast hlt
    have hmz : ∀ χ, χ ≠ principal → χ ≠ α → χ ≠ β → m χ = 0 := by
      intro χ h1 h2 h3
      by_cases hχ : χ ∈ B
      · by_contra hne
        have hge := hgap χ hχ h1 h2 h3
        have := hterm χ
        have : deg χ ≤ m χ * deg χ := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
        change Module.finrank ℂ (basis.representation χ).vector ≤ _ at this
        omega
      · exact hm0 χ hχ
    have hsub : ∀ {M : Type} [AddCommMonoid M] (f : basis.index → M),
        (∀ χ, m χ = 0 → f χ = 0) → ∑ χ, f χ = f principal + f α + f β := by
      intro M _ f hf
      rw [← Finset.sum_subset (Finset.subset_univ ({principal, α, β} : Finset basis.index))
        (fun χ _ hχ => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hχ
          exact hf χ (hmz χ hχ.1 hχ.2.1 hχ.2.2)),
        Finset.sum_insert (by simp [hαp.symm, hβp.symm]), Finset.sum_pair hαβ, add_assoc]
    have hΞt : Ξ.character t = 0 := hvan t (by rw [ht])
    have hexp := congrFun (character_eq_sum_multiplicity basis Ξ) t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm] at hexp
    rw [hΞt, hsub (fun χ => (m χ : ℂ) * (basis.representation χ).character t)
      (fun χ h => by rw [h, Nat.cast_zero, zero_mul]), hm1, hprincipal, hαt, hβt] at hexp
    have hint : (1 : ℤ) + (m α : ℤ) * q = (m β : ℤ) * (q - 1) := by
      have e : ((1 + (m α : ℤ) * q : ℤ) : ℂ) = (((m β : ℤ) * (q - 1) : ℤ) : ℂ) := by
        push_cast
        simp only [Pi.one_apply] at hexp
        linear_combination -hexp
      exact_mod_cast e
    have hbound := unitary_sign_multiplicity_bound (by exact_mod_cast hq) (Nat.cast_nonneg _) hint
    have hdegΞ : Module.finrank ℂ Ξ.vector = 1 + m α * (q ^ 2 - q + 1) + m β * (q ^ 2 - q) := by
      rw [hfin, hsub (fun χ => m χ * deg χ) (fun χ h => by rw [h, zero_mul]), hm1, hdegp]
      change 1 * 1 + m α * Module.finrank ℂ (basis.representation α).vector +
        m β * Module.finrank ℂ (basis.representation β).vector = _
      rw [hα1, hβ1, one_mul]
    rw [hdegΞ] at hltN
    have hltZ : (1 : ℤ) + (m α : ℤ) * ((q : ℤ) ^ 2 - q + 1) + (m β : ℤ) * ((q : ℤ) ^ 2 - q) <
        (q : ℤ) * ((q : ℤ) ^ 2 - q + 1) := by
      have e := hltN
      zify [hqq] at e
      exact e
    linarith
  have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : (0 : ℝ) < (q : ℝ) ^ 2 - q := by nlinarith
  have hμ : (0 : ℝ) < (q : ℝ) * (q ^ 2 - q + 1) := by nlinarith
  have hgapThm := principal_tensor_gap_bounds_singular_vanishing_character basis ideal 2
    principal hprincipal ((q : ℝ) ^ 2 - q) ((q : ℝ) * (q ^ 2 - q + 1)) hd hμ hdegB hΞ Θ hΘ hΘvan
  have hmin : min ((q : ℝ) * (q ^ 2 - q + 1)) (4 * ((q : ℝ) ^ 2 - q)) = 4 * ((q : ℝ) ^ 2 - q) :=
    min_eq_right (by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ q - 5)
        (by linarith : (0 : ℝ) ≤ q)) (by linarith : (0 : ℝ) ≤ q)])
  rw [hmin] at hgapThm
  refine ⟨hgapThm, ?_⟩
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hnn : (0 : ℝ) ≤ (Module.finrank ℂ Θ.vector : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_self_lt_mul_self hnn hlt]

end CFSG.Semidihedral.Principal
