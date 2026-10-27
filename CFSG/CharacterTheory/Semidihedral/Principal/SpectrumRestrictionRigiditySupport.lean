module

public import CFSG.CharacterTheory.Semidihedral.Principal.TensorGapBound

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal.SpectrumRigidity

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

universe u w

section Pairing

variable {H : Type u} [Group H] [Fintype H]

theorem pairing_add_right (f g₁ g₂ : H → ℂ) :
    characterPairing f (g₁ + g₂) = characterPairing f g₁ + characterPairing f g₂ := by
  unfold characterPairing
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairing_sub_right (f g₁ g₂ : H → ℂ) :
    characterPairing f (g₁ - g₂) = characterPairing f g₁ - characterPairing f g₂ := by
  unfold characterPairing
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pairing_smul_right (f g : H → ℂ) (c : ℂ) :
    characterPairing f (c • g) = c * characterPairing f g := by
  unfold characterPairing
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by ring

theorem pairing_sum_right (f : H → ℂ) {ι : Type*} (s : Finset ι) (g : ι → H → ℂ) :
    characterPairing f (∑ i ∈ s, g i) = ∑ i ∈ s, characterPairing f (g i) := by
  unfold characterPairing
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

end Pairing

section Multiplicity

variable {H : Type u} [Group H] [Fintype H] (basis : FiniteIrreducibleCharacterBasis H)

theorem exists_multiplicity (θ : FiniteComplexRepresentation.{u, w} H) :
    ∃ m : basis.index → ℕ,
      (∀ c, characterPairing θ.character (basis.representation c).character = m c) ∧
      Module.finrank ℂ θ.vector =
        ∑ c, m c * Module.finrank ℂ (basis.representation c).vector := by
  choose m hm using characterPairing_basis_natural basis θ
  exact ⟨m, hm, finrank_eq_sum_multiplicity basis θ m fun c => (hm c).symm⟩

theorem degree_pos (c : basis.index) : 0 < Module.finrank ℂ (basis.representation c).vector := by
  have h := irreducible_character_degree_ne_zero (basis.representation c) (basis.irreducible c)
  rw [FiniteComplexRepresentation.character, Representation.char_one] at h
  exact Nat.pos_of_ne_zero (by exact_mod_cast h)

theorem mul_degree_le {f : ℕ} (m : basis.index → ℕ)
    (hf : f = ∑ c, m c * Module.finrank ℂ (basis.representation c).vector) (c : basis.index) :
    m c * Module.finrank ℂ (basis.representation c).vector ≤ f := by
  rw [hf]
  exact Finset.single_le_sum (f := fun x => m x * Module.finrank ℂ (basis.representation x).vector)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

theorem degree_le_of_mem {f : ℕ} (m : basis.index → ℕ)
    (hf : f = ∑ c, m c * Module.finrank ℂ (basis.representation c).vector) (c : basis.index)
    (hc : 1 ≤ m c) : Module.finrank ℂ (basis.representation c).vector ≤ f :=
  (Nat.le_mul_of_pos_left _ hc).trans (mul_degree_le basis m hf c)

theorem sum_injective_le {f : ℕ} (m : basis.index → ℕ)
    (hf : f = ∑ c, m c * Module.finrank ℂ (basis.representation c).vector) {ι : Type*}
    [Fintype ι] (g : ι → basis.index) (hg : Function.Injective g) :
    ∑ i, m (g i) * Module.finrank ℂ (basis.representation (g i)).vector ≤ f := by
  rw [hf]
  calc ∑ i, m (g i) * Module.finrank ℂ (basis.representation (g i)).vector =
        ∑ c ∈ Finset.univ.image g, m c * Module.finrank ℂ (basis.representation c).vector :=
      (Finset.sum_image (f := fun c => m c * Module.finrank ℂ (basis.representation c).vector)
        (s := Finset.univ) fun i _ j _ hij => hg hij).symm
    _ ≤ ∑ c, m c * Module.finrank ℂ (basis.representation c).vector :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _

theorem character_eq_of_degree_le (θ : FiniteComplexRepresentation.{u, w} H)
    (m : basis.index → ℕ)
    (hm : ∀ c, characterPairing θ.character (basis.representation c).character = m c)
    (hf : Module.finrank ℂ θ.vector =
      ∑ c, m c * Module.finrank ℂ (basis.representation c).vector)
    (c : basis.index) (hc : 1 ≤ m c)
    (hdeg : Module.finrank ℂ θ.vector ≤ Module.finrank ℂ (basis.representation c).vector) :
    θ.character = (basis.representation c).character := by
  set deg : basis.index → ℕ := fun x => Module.finrank ℂ (basis.representation x).vector
    with hdegdef
  have hsplit := Finset.add_sum_erase Finset.univ (fun x => m x * deg x) (Finset.mem_univ c)
  have hpos := degree_pos basis c
  have hmc : m c * deg c ≥ deg c := Nat.le_mul_of_pos_left _ hc
  have hrest : ∑ x ∈ Finset.univ.erase c, m x * deg x = 0 := by
    change Module.finrank ℂ θ.vector = ∑ x, m x * deg x at hf
    change Module.finrank ℂ θ.vector ≤ deg c at hdeg
    omega
  have hm1 : m c = 1 := by
    change Module.finrank ℂ θ.vector = ∑ x, m x * deg x at hf
    change Module.finrank ℂ θ.vector ≤ deg c at hdeg
    have hle : m c * deg c ≤ 1 * deg c := by omega
    have := Nat.le_of_mul_le_mul_right hle hpos
    omega
  have hzero : ∀ x, x ≠ c → m x = 0 := by
    intro x hx
    have hx0 := (Finset.sum_eq_zero_iff.mp hrest) x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
    rcases Nat.mul_eq_zero.mp hx0 with h | h
    · exact h
    · exact absurd h (degree_pos basis x).ne'
  rw [character_eq_sum_multiplicity basis θ]
  rw [Finset.sum_eq_single c (fun x _ hx => by rw [hm x, hzero x hx, Nat.cast_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ c) h), hm c, hm1, Nat.cast_one, one_smul]

theorem exists_remove_constituent (θ : FiniteComplexRepresentation.{u, w} H)
    (m : basis.index → ℕ)
    (hm : ∀ c, characterPairing θ.character (basis.representation c).character = m c)
    (hf : Module.finrank ℂ θ.vector =
      ∑ c, m c * Module.finrank ℂ (basis.representation c).vector)
    (c : basis.index) (hc : 1 ≤ m c) :
    ∃ Ξ : FiniteComplexRepresentation.{u, u} H,
      Ξ.character = θ.character - (basis.representation c).character ∧
      Module.finrank ℂ Ξ.vector + Module.finrank ℂ (basis.representation c).vector =
        Module.finrank ℂ θ.vector := by
  set m' : basis.index → ℕ := Function.update m c (m c - 1) with hm'def
  have hsplit : ∀ x, m x = m' x + if x = c then 1 else 0 := by
    intro x
    by_cases hx : x = c
    · subst hx
      rw [hm'def, Function.update_self, ite_eq_left rfl]
      omega
    · rw [hm'def, Function.update_of_ne hx, ite_eq_right hx, add_zero]
  obtain ⟨Ξ, hΞ⟩ := exists_character_eq_sum basis m'
  refine ⟨Ξ, ?_, ?_⟩
  · rw [hΞ, character_eq_sum_multiplicity basis θ]
    have hθ : (∑ x, characterPairing θ.character (basis.representation x).character •
        (basis.representation x).character) =
        ∑ x, ((m' x : ℂ) • (basis.representation x).character +
          if x = c then (basis.representation x).character else 0) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hm x, hsplit x]
      by_cases hx : x = c
      · rw [ite_eq_left hx, ite_eq_left hx]
        push_cast
        rw [add_smul, one_smul]
      · rw [ite_eq_right hx, ite_eq_right hx]
        push_cast
        rw [add_zero, add_zero]
    rw [hθ, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ c, ite_eq_left
      (Finset.mem_univ c), add_sub_cancel_right]
  · have hΞpair : ∀ x, (m' x : ℂ) = characterPairing Ξ.character
        (basis.representation x).character := by
      intro x
      rw [hΞ, characterPairing_sum_smul_basis]
    rw [finrank_eq_sum_multiplicity basis Ξ m' hΞpair, hf]
    have hsum : ∑ x, m x * Module.finrank ℂ (basis.representation x).vector =
        ∑ x, (m' x * Module.finrank ℂ (basis.representation x).vector +
          if x = c then Module.finrank ℂ (basis.representation x).vector else 0) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsplit x]
      by_cases hx : x = c
      · rw [ite_eq_left hx, ite_eq_left hx, add_mul, one_mul]
      · rw [ite_eq_right hx, ite_eq_right hx, add_zero, add_zero]
    rw [hsum, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ c,
      ite_eq_left (Finset.mem_univ c)]

end Multiplicity

section Arithmetic

theorem lt_sq_of_first_positive {q f₁ f₂ f₃ : ℤ} (hq : 1 ≤ q) (hf₁ : 0 < f₁) (hf₂ : 1 < f₂)
    (hsum : 1 + 1 * f₁ + -1 * f₂ + -1 * f₃ = 0) (hprod : f₁ * f₂ = q ^ 2 * f₃) :
    f₁ * (f₂ - q ^ 2) = q ^ 2 * (1 - f₂) ∧ f₂ < q ^ 2 := by
  have h : f₁ * (f₂ - q ^ 2) = q ^ 2 * (1 - f₂) := by linear_combination hprod - q ^ 2 * hsum
  refine ⟨h, ?_⟩
  by_contra hlt
  have h1 : 0 ≤ f₁ * (f₂ - q ^ 2) := mul_nonneg hf₁.le (by linarith)
  have h2 : q ^ 2 * (1 - f₂) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

theorem lt_sq_of_second_positive {q f₁ f₂ f₃ : ℤ} (hq : 1 ≤ q) (hf₁ : 1 < f₁) (hf₂ : 0 < f₂)
    (hsum : 1 + -1 * f₁ + 1 * f₂ + -1 * f₃ = 0) (hprod : f₁ * f₂ = q ^ 2 * f₃) :
    f₁ < q ^ 2 := by
  have h : f₂ * (f₁ - q ^ 2) = q ^ 2 * (1 - f₁) := by linear_combination hprod - q ^ 2 * hsum
  by_contra hlt
  have h1 : 0 ≤ f₂ * (f₁ - q ^ 2) := mul_nonneg hf₂.le (by linarith)
  have h2 : q ^ 2 * (1 - f₁) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

theorem excess_product_of_third_positive {q f₁ f₂ f₃ : ℤ}
    (hsum : 1 + -1 * f₁ + -1 * f₂ + 1 * f₃ = 0) (hprod : f₁ * f₂ = q ^ 2 * f₃) :
    (f₁ - q ^ 2) * (f₂ - q ^ 2) = q ^ 2 * (q ^ 2 - 1) := by
  linear_combination hprod + q ^ 2 * hsum

theorem excess_le_of_cube_le {q f₁ f₂ : ℤ} (hq : 2 ≤ q) (hf₁ : q ^ 3 ≤ f₁)
    (h : (f₁ - q ^ 2) * (f₂ - q ^ 2) = q ^ 2 * (q ^ 2 - 1)) :
    q ^ 2 < f₂ ∧ f₂ ≤ q ^ 2 + q + 1 := by
  have hq2 : 0 < q ^ 2 * (q - 1) := mul_pos (by positivity) (by linarith)
  have hpos1 : q ^ 2 * (q - 1) ≤ f₁ - q ^ 2 := by nlinarith
  have hrhs : 0 < q ^ 2 * (q ^ 2 - 1) := by
    have : 0 < q ^ 2 - 1 := by nlinarith
    positivity
  have hgt : 0 < f₂ - q ^ 2 := by
    by_contra hle
    have : (f₁ - q ^ 2) * (f₂ - q ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hle)
    linarith
  refine ⟨by linarith, ?_⟩
  have hle : q ^ 2 * (q - 1) * (f₂ - q ^ 2) ≤ q ^ 2 * (q - 1) * (q + 1) := by
    have := mul_le_mul_of_nonneg_right hpos1 hgt.le
    nlinarith
  have := le_of_mul_le_mul_left hle hq2
  linarith

theorem eq_cube_of_excess {q f₁ : ℤ} (hq : 2 ≤ q)
    (h : (f₁ - q ^ 2) * (q + 1) = q ^ 2 * (q ^ 2 - 1)) : f₁ = q ^ 3 := by
  have h' : (f₁ - q ^ 2) * (q + 1) = (q ^ 2 * (q - 1)) * (q + 1) := by rw [h]; ring
  have := mul_right_cancel₀ (by positivity : (q + 1 : ℤ) ≠ 0) h'
  linear_combination this


theorem sq_le_cube {q : ℤ} (hq : 1 ≤ q) : q ^ 2 ≤ q ^ 3 := by
  have := pow_le_pow_right₀ hq (show 2 ≤ 3 by norm_num)
  exact this

theorem sq_add_lt_cube {q : ℤ} (hq : 2 ≤ q) : q ^ 2 + q + 1 < q ^ 3 := by nlinarith

theorem three_sq_lt_gap {q : ℤ} (hq : 5 ≤ q) : 3 * q ^ 2 + q < 3 * (q * (q ^ 2 - q + 1)) := by
  nlinarith

theorem gap_le_cube {q : ℤ} (hq : 1 ≤ q) : q * (q ^ 2 - q + 1) ≤ q ^ 3 := by nlinarith

theorem exceptional_degree_bound {q k a₀ a₁ a₂ a₃ a₄ b : ℤ} (hq : 5 ≤ q) (hk : 2 ≤ k)
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄)
    (hb : b = a₀ + a₁ + 1) (h23 : a₂ + a₃ = b) (h24 : a₂ = a₀ + a₄) :
    3 * q ^ 3 + 2 * q ^ 2 - 2 * q < (2 * k - 1) * b * (q ^ 3 + 1) + a₂ * (q ^ 2 - q + 1) +
      a₃ * (q * (q ^ 2 - q + 1)) + a₄ * (q ^ 2 - q) := by
  have hq3 : 0 < q ^ 3 + 1 := by positivity
  have hd2 : 0 ≤ q ^ 2 - q + 1 := by nlinarith
  have hd3 : 0 ≤ q * (q ^ 2 - q + 1) := by nlinarith
  have hd4 : 0 ≤ q ^ 2 - q := by nlinarith
  have hk3 : 3 ≤ 2 * k - 1 := by linarith
  have hbase : 3 * b * (q ^ 3 + 1) ≤ (2 * k - 1) * b * (q ^ 3 + 1) := by
    have := mul_le_mul_of_nonneg_right hk3 (by linarith : (0 : ℤ) ≤ b)
    nlinarith
  have hA := mul_nonneg ha₂ hd2
  have hB := mul_nonneg ha₃ hd3
  have hC := mul_nonneg ha₄ hd4
  rcases (show 2 ≤ b ∨ b = 1 by omega) with h2 | h1
  · nlinarith
  · have h0 : a₀ = 0 := by omega
    have h1' : a₁ = 0 := by omega
    subst h0 h1'
    rcases (show (a₂ = 0 ∧ a₃ = 1) ∨ (a₂ = 1 ∧ a₃ = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · subst h1
      nlinarith
    · have : a₄ = 1 := by omega
      subst this h1
      nlinarith

theorem small_excess_of_large {q f₁ f₂ : ℤ} (hq : 5 ≤ q)
    (hf₁ : 3 * q ^ 3 + 2 * q ^ 2 - 2 * q < f₁)
    (h : (f₁ - q ^ 2) * (f₂ - q ^ 2) = q ^ 2 * (q ^ 2 - 1)) :
    q ^ 2 < f₂ ∧ 3 * f₂ < 3 * q ^ 2 + q := by
  have hX : 0 < 3 * q ^ 3 + q ^ 2 - 2 * q + 1 := by nlinarith
  have hpos1 : 3 * q ^ 3 + q ^ 2 - 2 * q + 1 ≤ f₁ - q ^ 2 := by linarith
  have hrhs : 0 < q ^ 2 * (q ^ 2 - 1) := by
    have : 0 < q ^ 2 - 1 := by nlinarith
    positivity
  have hgt : 0 < f₂ - q ^ 2 := by
    by_contra hle
    have : (f₁ - q ^ 2) * (f₂ - q ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hle)
    linarith
  refine ⟨by linarith, ?_⟩
  by_contra hge
  have h3 : q ≤ 3 * (f₂ - q ^ 2) := by linarith [not_lt.mp hge]
  have hle : (3 * q ^ 3 + q ^ 2 - 2 * q + 1) * (f₂ - q ^ 2) ≤ q ^ 2 * (q ^ 2 - 1) := by
    have := mul_le_mul_of_nonneg_right hpos1 hgt.le
    linarith
  have hle2 : (3 * q ^ 3 + q ^ 2 - 2 * q + 1) * q ≤
      (3 * q ^ 3 + q ^ 2 - 2 * q + 1) * (3 * (f₂ - q ^ 2)) :=
    mul_le_mul_of_nonneg_left h3 hX.le
  nlinarith

end Arithmetic


section Exceptional

variable {H : Type u} [Group H] [Fintype H] (basis : FiniteIrreducibleCharacterBasis H)

theorem exceptional_lower_bound {q k : ℕ} (hq : 5 ≤ q) (hk : 2 ≤ k) {f₁ : ℕ}
    (a : basis.index → ℕ)
    (hf₁sum : f₁ = ∑ c, a c * Module.finrank ℂ (basis.representation c).vector)
    (principal α₁ α₂ α₃ α₄ : basis.index) (Ψ : Fin (k - 1) → basis.index)
    (N : Fin k → basis.index)
    (hdistinct : Function.Injective (Sum.elim ![principal, α₁, α₂, α₃, α₄] (Sum.elim Ψ N)))
    (hd₂ : (Module.finrank ℂ (basis.representation α₂).vector : ℤ) = q ^ 2 - q + 1)
    (hd₃ : (Module.finrank ℂ (basis.representation α₃).vector : ℤ) = q * (q ^ 2 - q + 1))
    (hd₄ : (Module.finrank ℂ (basis.representation α₄).vector : ℤ) = q ^ 2 - q)
    (hΨ : ∀ j, (Module.finrank ℂ (basis.representation (Ψ j)).vector : ℤ) = q ^ 3 + 1)
    (hN : ∀ l, (Module.finrank ℂ (basis.representation (N l)).vector : ℤ) = q ^ 3 + 1)
    (hΨb : ∀ j, (a (Ψ j) : ℤ) = a principal + a α₁ + 1)
    (hNb : ∀ l, (a (N l) : ℤ) = a principal + a α₁ + 1)
    (h23 : (a α₂ : ℤ) + a α₃ = a principal + a α₁ + 1)
    (h24 : (a α₂ : ℤ) = a principal + a α₄) :
    3 * (q : ℤ) ^ 3 + 2 * q ^ 2 - 2 * q < f₁ := by
  have hinj := sum_injective_le basis a hf₁sum _ hdistinct
  have hexpand : ∑ i, a (Sum.elim ![principal, α₁, α₂, α₃, α₄] (Sum.elim Ψ N) i) *
      Module.finrank ℂ (basis.representation
        (Sum.elim ![principal, α₁, α₂, α₃, α₄] (Sum.elim Ψ N) i)).vector =
      a principal * Module.finrank ℂ (basis.representation principal).vector +
      a α₁ * Module.finrank ℂ (basis.representation α₁).vector +
      a α₂ * Module.finrank ℂ (basis.representation α₂).vector +
      a α₃ * Module.finrank ℂ (basis.representation α₃).vector +
      a α₄ * Module.finrank ℂ (basis.representation α₄).vector +
      (∑ j, a (Ψ j) * Module.finrank ℂ (basis.representation (Ψ j)).vector +
        ∑ l, a (N l) * Module.finrank ℂ (basis.representation (N l)).vector) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_five]
    rfl
  rw [hexpand] at hinj
  have hinjZ := (Nat.cast_le (α := ℤ)).mpr hinj
  push_cast at hinjZ
  set b : ℤ := (a principal : ℤ) + a α₁ + 1 with hbdef
  have hΨsum : ∑ j, (a (Ψ j) : ℤ) * (Module.finrank ℂ (basis.representation (Ψ j)).vector : ℤ) =
      ((k : ℤ) - 1) * (b * (q ^ 3 + 1)) := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hΨb j, hΨ j], Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ k)]
    simp
  have hNsum : ∑ l, (a (N l) : ℤ) * (Module.finrank ℂ (basis.representation (N l)).vector : ℤ) =
      (k : ℤ) * (b * (q ^ 3 + 1)) := by
    rw [Finset.sum_congr rfl fun l _ => by rw [hNb l, hN l], Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hΨsum, hNsum, hd₂, hd₃, hd₄] at hinjZ
  have hexc := exceptional_degree_bound (q := (q : ℤ)) (k := (k : ℤ)) (by exact_mod_cast hq)
    (by exact_mod_cast hk)
    (Nat.cast_nonneg (a principal)) (Nat.cast_nonneg (a α₁)) (Nat.cast_nonneg (a α₂))
    (Nat.cast_nonneg (a α₃)) (Nat.cast_nonneg (a α₄)) hbdef h23 h24
  have hp0 : 0 ≤ (a principal : ℤ) * Module.finrank ℂ (basis.representation principal).vector :=
    by positivity
  have hp1 : 0 ≤ (a α₁ : ℤ) * Module.finrank ℂ (basis.representation α₁).vector := by positivity
  linarith [hinjZ, hexc, hp0, hp1]

end Exceptional

end CFSG.Semidihedral.Principal.SpectrumRigidity
