module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseGram
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseRows

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGeneralBase

open CFSG.Wreathed.ConditionalFourier

variable {m : ℕ} [NeZero m] {A : Type*} [Group A] [Fintype A] {σ υ : A} {ζ : ℂ}

omit [NeZero m] in
theorem baseMultiplicity_comp (lam : ZMod m → ZMod m → A →* ℂ) (χ : A → ℂ) (φ : MulAut A)
    (hχ : ∀ x, χ (φ x) = χ x) (i j i' j' : ZMod m) (hlam : ∀ x, lam i j (φ x) = lam i' j' x) :
    baseMultiplicity lam χ i j = baseMultiplicity lam χ i' j' := by
  unfold baseMultiplicity
  congr 1
  rw [← Fintype.sum_equiv φ.toEquiv (fun x => χ (φ x) * conj (lam i j (φ x)))
    (fun x => χ x * conj (lam i j x)) (fun x => rfl)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hχ, hlam]

variable (hc : Commute σ υ) (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤)
  (hζ : IsPrimitiveRoot ζ m) (lam : ZMod m → ZMod m → A →* ℂ)
  (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val)
  (h6 : Fin 6 → MulAut A)
  (h6σ : ∀ k, h6 k σ = ![σ, υ, υ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹] k)
  (h6υ : ∀ k, h6 k υ = ![υ, σ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹, υ] k)

include hc hgen hζ hlam h6σ h6υ in
theorem baseColumn_symm (χ : A → ℂ) (hχ : ∀ k x, χ (h6 k x) = χ x) (v : ℕ → Fin 2 → ℂ)
    (q₀ : ℂ) (i j : ZMod m) :
    baseColumn lam χ ζ v q₀ i j = baseColumn lam χ ζ v q₀ j i ∧
      baseColumn lam χ ζ v q₀ i j = baseColumn lam χ ζ v q₀ j (-i - j) := by
  have h1 := baseMultiplicity_comp lam χ (h6 1) (hχ 1) i j j i (fun x => by
    have h := lam_comp_six hc hgen hζ lam hlam h6 h6σ h6υ (i, j) 1 x
    simpa using h)
  have h2 := baseMultiplicity_comp lam χ (h6 2) (hχ 2) i j j (-i - j) (fun x => by
    have h := lam_comp_six hc hgen hζ lam hlam h6 h6σ h6υ (i, j) 2 x
    simpa using h)
  refine ⟨?_, ?_⟩
  · unfold baseColumn
    rw [h1, show -j - i = -i - j by ring]
    ring
  · unfold baseColumn
    rw [h2, show -j - (-i - j) = i by ring]
    ring

omit [NeZero m] in
theorem baseColumn_zero (χ : A → ℂ) (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ) :
    baseColumn lam χ ζ v q₀ 0 0 = 0 := by
  unfold baseColumn
  simp only [sub_self, neg_zero, zmodFourier_zero, add_zero, mul_zero]

include hc hgen hζ hlam in
theorem baseColumn_principal (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ)
    (hv : ∀ j : ZMod m, zmodFourier ζ (fun k => v k 1) j = 0) {i j : ZMod m}
    (hij : (i, j) ≠ (0, 0)) : baseColumn lam (fun _ => 1) ζ v q₀ i j = 1 := by
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h0 : baseMultiplicity lam (fun _ => (1 : ℂ)) 0 0 = 1 := by
    unfold baseMultiplicity
    simp only [lam_zero hc hgen lam hlam, map_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hcard
  have hij' : ¬ (i = 0 ∧ j = 0) := fun h => hij (by rw [h.1, h.2])
  have h1 : baseMultiplicity lam (fun _ => (1 : ℂ)) i j = 0 := by
    unfold baseMultiplicity
    have hs := sum_linearCharacter hc hgen hζ (lam i j) (hlam i j).1 (hlam i j).2
    rw [ite_eq_right hij'] at hs
    simp only [one_mul]
    rw [← map_sum, hs, map_zero, mul_zero]
  unfold baseColumn
  rw [h0, h1, hv, hv, hv]
  ring

omit [Group A] [Fintype A] in
theorem column_orthogonal {ι : Type*} (B : Finset ι) (P : Finset A) (Z : ι → ℕ → ℂ)
    (W : ι → A → ℂ) (col : ι → ℂ) (b : ℕ → ℂ) (α : A → ℂ)
    (hcol : ∀ χ ∈ B, (m : ℂ) ^ 2 * col χ =
      ∑ k ∈ Finset.Ico 1 m, b k * Z χ k + ∑ x ∈ P, α x * W χ x)
    (T : ι → ℂ) (hZ : ∀ k ∈ Finset.Ico 1 m, ∑ χ ∈ B, Z χ k * conj (T χ) = 0)
    (hW : ∀ x ∈ P, ∑ χ ∈ B, W χ x * conj (T χ) = 0) :
    ∑ χ ∈ B, col χ * conj (T χ) = 0 := by
  have hm0 : (m : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast NeZero.ne m)
  have h : (m : ℂ) ^ 2 * ∑ χ ∈ B, col χ * conj (T χ) = 0 := by
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun χ hχ => by rw [← mul_assoc, hcol χ hχ]]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := B)]
    rw [Finset.sum_eq_zero fun k hk => by
        rw [Finset.sum_congr rfl fun χ _ => mul_assoc (b k) (Z χ k) (conj (T χ)),
          ← Finset.mul_sum, hZ k hk, mul_zero],
      Finset.sum_eq_zero fun x hx => by
        rw [Finset.sum_congr rfl fun χ _ => mul_assoc (α x) (W χ x) (conj (T χ)),
          ← Finset.mul_sum, hW x hx, mul_zero], add_zero]
  exact (mul_eq_zero.mp h).resolve_left hm0

end CFSG.Wreathed.ConditionalGeneralBase
