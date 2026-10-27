module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitBasis

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix CFSG.AGLEmbedding.LinearThreeKit

variable {K : Type*} [Field K]

theorem mulVec_sum_smul {S : Matrix (Fin 3) (Fin 3) K} {b : Fin 3 → Fin 3 → K} {r : Fin 3 → K}
    (hs : ∀ i, S *ᵥ b i = r i • b i) (c : Fin 3 → K) :
    S *ᵥ (∑ i, c i • b i) = ∑ i, (c i * r i) • b i := by
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, hs, smul_smul]

theorem coeff_mul_sub_eq_zero {S : Matrix (Fin 3) (Fin 3) K} {b : Fin 3 → Fin 3 → K}
    (hb : LinearIndependent K b) {r : Fin 3 → K} (hs : ∀ i, S *ᵥ b i = r i • b i)
    {γ : Fin 3 → K} {l : K} (hv : S *ᵥ (∑ i, γ i • b i) = l • ∑ i, γ i • b i) (i : Fin 3) :
    γ i * (r i - l) = 0 := by
  rw [mulVec_sum_smul hs, Finset.smul_sum] at hv
  have h0 : ∑ i, (γ i * r i - l * γ i) • b i = 0 := by
    have : ∑ i, (γ i * r i - l * γ i) • b i =
        ∑ i, (γ i * r i) • b i - ∑ i, l • γ i • b i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [sub_smul, mul_smul]
    rw [this, hv, sub_self]
  have := Fintype.linearIndependent_iff.mp hb _ h0 i
  linear_combination this

theorem smul_basis_mem_of_invariant {S : Matrix (Fin 3) (Fin 3) K} {b : Fin 3 → Fin 3 → K}
    {r : Fin 3 → K} (hs : ∀ i, S *ᵥ b i = r i • b i) (hr : Function.Injective r)
    {W : Submodule K (Fin 3 → K)} (hW : ∀ v ∈ W, S *ᵥ v ∈ W) {c : Fin 3 → K}
    (hc : ∑ i, c i • b i ∈ W) (i : Fin 3) : c i • b i ∈ W := by
  have hthree : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide
  obtain ⟨j, k, hij, hik, hjk⟩ := hthree i
  have hall : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ l, l = i ∨ l = j ∨ l = k := by decide
  set v : Fin 3 → K := ∑ l, c l • b l with hv
  have hq : S *ᵥ (S *ᵥ v) - (r j + r k) • (S *ᵥ v) + (r j * r k) • v ∈ W :=
    W.add_mem (W.sub_mem (hW _ (hW _ hc)) (W.smul_mem _ (hW _ hc))) (W.smul_mem _ hc)
  have hsum : S *ᵥ (S *ᵥ v) - (r j + r k) • (S *ᵥ v) + (r j * r k) • v =
      ∑ l, (c l * ((r l - r j) * (r l - r k))) • b l := by
    rw [hv, mulVec_sum_smul hs, mulVec_sum_smul hs]
    simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [smul_smul, ← sub_smul, ← add_smul]
    congr 1
    ring
  rw [hsum, Finset.sum_eq_single i] at hq
  · have hne : (r i - r j) * (r i - r k) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr fun h => hij (hr h)) (sub_ne_zero.mpr fun h => hik (hr h))
    have := W.smul_mem ((r i - r j) * (r i - r k))⁻¹ hq
    have e : ((r i - r j) * (r i - r k))⁻¹ * (c i * ((r i - r j) * (r i - r k))) = c i := by
      rw [mul_comm (c i), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rwa [smul_smul, e] at this
  · intro l _ hl
    rcases hall i j k hij hik hjk l with h | h | h
    · exact absurd h hl
    · subst h; simp
    · subst h; simp
  · intro h; exact absurd (Finset.mem_univ i) h

theorem exists_basis_mem_of_invariant {S : Matrix (Fin 3) (Fin 3) K} {b : Fin 3 → Fin 3 → K}
    (hb : LinearIndependent K b) {r : Fin 3 → K} (hs : ∀ i, S *ᵥ b i = r i • b i)
    (hr : Function.Injective r) {W : Submodule K (Fin 3 → K)} (hW0 : W ≠ ⊥)
    (hWS : ∀ v ∈ W, S *ᵥ v ∈ W) : ∃ i, b i ∈ W := by
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW0
  obtain ⟨c, hc⟩ := exists_sum_smul_eq hb w
  have hcw : ∑ i, c i • b i ∈ W := hc ▸ hwW
  by_contra hno
  push Not at hno
  apply hw0
  rw [← hc]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hmem := smul_basis_mem_of_invariant hs hr hWS hcw i
  by_contra hne
  have hci : c i ≠ 0 := fun h => hne (by rw [h, zero_smul])
  apply hno i
  have := W.smul_mem (c i)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hci, one_smul] at this

theorem eq_one_of_invariant {S A : Matrix (Fin 3) (Fin 3) K} {b : Fin 3 → Fin 3 → K}
    (hb : LinearIndependent K b) {r : Fin 3 → K} (hs : ∀ i, S *ᵥ b i = r i • b i)
    (hr : Function.Injective r) (hr0 : ∀ i, r i ≠ 0) {c : K} (hc3 : c ^ 3 = 1)
    (hAS : A * S = c • (S * A)) (hAinj : ∀ v, A *ᵥ v = 0 → v = 0)
    {W : Submodule K (Fin 3 → K)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) (hWS : ∀ v ∈ W, S *ᵥ v ∈ W)
    (hWA : ∀ v ∈ W, A *ᵥ v ∈ W) : c = 1 := by
  by_contra hc1
  have hc0 : c ≠ 0 := fun h => by rw [h] at hc3; simp at hc3
  have hc2 : c ^ 2 ≠ 1 := fun h => hc1 (by
    calc c = c * c ^ 2 := by rw [h, mul_one]
      _ = c ^ 3 := by ring
      _ = 1 := hc3)
  have hSA : S * A = c⁻¹ • (A * S) := by
    rw [hAS, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hstep : ∀ i, b i ∈ W → ∃ l, b l ∈ W ∧ r l = c⁻¹ * r i := by
    intro i hi
    have hAi : A *ᵥ b i ∈ W := hWA _ hi
    obtain ⟨γ, hγ⟩ := exists_sum_smul_eq hb (A *ᵥ b i)
    have hγW : ∑ l, γ l • b l ∈ W := hγ ▸ hAi
    have hSv : S *ᵥ (∑ l, γ l • b l) = (c⁻¹ * r i) • ∑ l, γ l • b l := by
      rw [hγ, Matrix.mulVec_mulVec, hSA, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hs,
        Matrix.mulVec_smul, smul_smul]
    have hne : ∃ l, γ l ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : A *ᵥ b i = 0 := by
        rw [← hγ]; exact Finset.sum_eq_zero fun l _ => by rw [hall l, zero_smul]
      exact (hb.ne_zero i) (hAinj _ h0)
    obtain ⟨l, hl⟩ := hne
    have hcoef := coeff_mul_sub_eq_zero hb hs hSv l
    refine ⟨l, ?_, ?_⟩
    · have hmem := smul_basis_mem_of_invariant hs hr hWS hγW l
      have := W.smul_mem (γ l)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hl, one_smul] at this
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hcoef).resolve_left hl)
  obtain ⟨i₀, hi₀⟩ := exists_basis_mem_of_invariant hb hs hr hW0 hWS
  obtain ⟨i₁, hi₁, hr₁⟩ := hstep i₀ hi₀
  obtain ⟨i₂, hi₂, hr₂⟩ := hstep i₁ hi₁
  have hci : c⁻¹ ≠ 1 := fun h => hc1 (by simpa using congrArg (·⁻¹) h)
  have hne_of : ∀ (x : K) (i j : Fin 3), x ≠ 1 → r j = x * r i → j ≠ i := by
    intro x i j hx hrj hji
    subst hji
    apply hx
    have : (x - 1) * r j = 0 := by linear_combination -hrj
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (hr0 j)
  have hd01 : i₁ ≠ i₀ := hne_of c⁻¹ i₀ i₁ hci hr₁
  have hd12 : i₂ ≠ i₁ := hne_of c⁻¹ i₁ i₂ hci hr₂
  have hd02 : i₂ ≠ i₀ := by
    refine hne_of (c⁻¹ * c⁻¹) i₀ i₂ ?_ (by rw [hr₂, hr₁, mul_assoc])
    intro h
    apply hc2
    have : c ^ 2 = (c⁻¹ * c⁻¹)⁻¹ := by rw [mul_inv, inv_inv, pow_two]
    rw [this, h, inv_one]
  have hall : ∀ i j k : Fin 3, j ≠ i → k ≠ j → k ≠ i → ∀ l, l = i ∨ l = j ∨ l = k := by decide
  have hbW : ∀ l, b l ∈ W := fun l => by
    rcases hall i₀ i₁ i₂ hd01 hd12 hd02 l with rfl | rfl | rfl <;> assumption
  apply hWt
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨d, hd⟩ := exists_sum_smul_eq hb v
  rw [← hd]
  exact W.sum_mem fun l _ => W.smul_mem _ (hbW l)

theorem exists_mulVec_eq_smul_of_commute {S A : Matrix (Fin 3) (Fin 3) K}
    {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b) {r : Fin 3 → K}
    (hs : ∀ i, S *ᵥ b i = r i • b i) (hr : Function.Injective r) (hAS : A * S = S * A)
    (i : Fin 3) : ∃ a : K, A *ᵥ b i = a • b i := by
  obtain ⟨γ, hγ⟩ := exists_sum_smul_eq hb (A *ᵥ b i)
  have hSv : S *ᵥ (∑ l, γ l • b l) = r i • ∑ l, γ l • b l := by
    rw [hγ, Matrix.mulVec_mulVec, ← hAS, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_smul]
  refine ⟨γ i, ?_⟩
  rw [← hγ]
  rw [Finset.sum_eq_single i]
  · intro l _ hl
    have := coeff_mul_sub_eq_zero hb hs hSv l
    have hne : r l - r i ≠ 0 := sub_ne_zero.mpr fun h => hl (hr h)
    rw [(mul_eq_zero.mp this).resolve_right hne, zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

end CFSG.HardMathSupport.Curtis.Coordinator
