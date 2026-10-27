module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.OrthCore

public section

open Matrix
open scoped commutatorElement

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG CFSG.Open CFSG.CGT.PushingUpLit.CGT6M

section Bridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem good_of_formula (S : Matrix ι ι K) (hS : ∀ v w, v ⬝ᵥ S *ᵥ w = w ⬝ᵥ S *ᵥ v)
    (hnd : ∀ x, (∀ y, x ⬝ᵥ S *ᵥ y = 0) → x = 0) (h2 : (2 : K) ≠ 0) :
    Good (Matrix.toBilin' S) :=
  ⟨fun x y => by simpa [Matrix.toBilin'_apply'] using hS x y,
    fun x hx => hnd x (fun y => by simpa [Matrix.toBilin'_apply'] using hx y), h2⟩

theorem statedOmega_eq (S : Matrix ι ι K) (G : Good (Matrix.toBilin' S)) {Q : (ι → K) → K}
    (hQ : ∀ v, Q v = 2⁻¹ * (v ⬝ᵥ S *ᵥ v)) :
    StatedOmega Q = omegaGroup (Matrix.toBilin' S) := by
  set B := Matrix.toBilin' S with hB
  have hQ' : ∀ v, Q v = 2⁻¹ * B v v := fun v => by rw [hQ v, hB, Matrix.toBilin'_apply']
  have hset : {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} =
      (isomGroup B : Set (GL ι K)) := by
    ext A
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_isomGroup_iff, hQ']
    constructor
    · intro h x y
      have h' : ∀ v, B ((A : Matrix ι ι K) *ᵥ v) ((A : Matrix ι ι K) *ᵥ v) = B v v := fun v =>
        mul_left_cancel₀ (inv_ne_zero G.two) (h v)
      have h1 := h' (x + y)
      rw [Matrix.mulVec_add] at h1
      simp only [map_add, LinearMap.add_apply] at h1
      rw [G.symm ((A : Matrix ι ι K) *ᵥ y) ((A : Matrix ι ι K) *ᵥ x), G.symm y x, h' x, h' y] at h1
      exact mul_left_cancel₀ G.two (by linear_combination h1)
    · intro h v
      rw [h v v]
  show ⁅Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v},
    Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}⁆ = ⁅isomGroup B, isomGroup B⁆
  rw [hset, Subgroup.closure_eq]

theorem orth_involution [CharP K 5] [Finite K] (S : Matrix ι ι K)
    (hS : ∀ v w, v ⬝ᵥ S *ᵥ w = w ⬝ᵥ S *ᵥ v)
    (hnd : ∀ x, (∀ y, x ⬝ᵥ S *ᵥ y = 0) → x = 0) {Q : (ι → K) → K}
    (hQ : ∀ v, Q v = 2⁻¹ * (v ⬝ᵥ S *ᵥ v)) (hD : 7 ≤ Fintype.card ι)
    (z : StatedProj (StatedOmega Q)) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    (∃ Φ : C55 →* StatedProj (StatedOmega Q), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹) ∨
    (∃ X Y : StatedProj (StatedOmega Q), X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧ Commute ⁅Y, X⁆ X ∧
      Commute ⁅Y, X⁆ Y ∧ ⁅Y, X⁆ ≠ 1 ∧ z * X * z⁻¹ = X⁻¹) := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
    have h1 : (1 : K) = 0 := by linear_combination h5 - 2 * h
    exact one_ne_zero h1
  have G := good_of_formula S hS hnd h2
  have hΩ := statedOmega_eq S G hQ
  generalize StatedOmega Q = H at hΩ z hz1 hz2 ⊢
  subst hΩ
  exact orth_core G hD z hz1 hz2

end Bridge
section Plus

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def Splus : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 1 0

theorem Splus_bil (v w : Fin n ⊕ Fin n → K) :
    v ⬝ᵥ Splus n K *ᵥ w = ∑ i, (v (.inl i) * w (.inr i) + v (.inr i) * w (.inl i)) := by
  simp [Splus, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks,
    Finset.sum_add_distrib, Matrix.one_apply]

theorem Splus_symm (v w : Fin n ⊕ Fin n → K) : v ⬝ᵥ Splus n K *ᵥ w = w ⬝ᵥ Splus n K *ᵥ v := by
  rw [Splus_bil, Splus_bil]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem Splus_nd (x : Fin n ⊕ Fin n → K) (hx : ∀ y, x ⬝ᵥ Splus n K *ᵥ y = 0) : x = 0 := by
  funext i
  rcases i with j | j
  · have := hx (Pi.single (.inr j) 1)
    rw [Splus_bil] at this
    simpa [Pi.single_apply] using this
  · have := hx (Pi.single (.inl j) 1)
    rw [Splus_bil] at this
    simpa [Pi.single_apply] using this

theorem Splus_quad (h2 : (2 : K) ≠ 0) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n K v = 2⁻¹ * (v ⬝ᵥ Splus n K *ᵥ v) := by
  rw [Splus_bil, StatedQuadPlus]
  have : ∑ i, (v (.inl i) * v (.inr i) + v (.inr i) * v (.inl i)) =
      2 * ∑ i, v (.inl i) * v (.inr i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  field_simp

end Plus

section Odd

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def Sodd : Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K :=
  Matrix.of fun i j =>
  match i, j with
  | .inl a, .inr (.inl b) => if a = b then 1 else 0
  | .inr (.inl a), .inl b => if a = b then 1 else 0
  | .inr (.inr _), .inr (.inr _) => 2
  | _, _ => 0

theorem Sodd_bil (v w : Fin n ⊕ Fin n ⊕ Unit → K) :
    v ⬝ᵥ Sodd n K *ᵥ w = ∑ i, (v (.inl i) * w (.inr (.inl i)) + v (.inr (.inl i)) * w (.inl i)) +
      2 * (v (.inr (.inr ())) * w (.inr (.inr ()))) := by
  simp [Sodd, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Finset.sum_add_distrib]
  ring

theorem Sodd_symm (v w : Fin n ⊕ Fin n ⊕ Unit → K) :
    v ⬝ᵥ Sodd n K *ᵥ w = w ⬝ᵥ Sodd n K *ᵥ v := by
  rw [Sodd_bil, Sodd_bil]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

theorem Sodd_nd (h2 : (2 : K) ≠ 0) (x : Fin n ⊕ Fin n ⊕ Unit → K)
    (hx : ∀ y, x ⬝ᵥ Sodd n K *ᵥ y = 0) : x = 0 := by
  funext i
  rcases i with j | j | j
  · have := hx (Pi.single (.inr (.inl j)) 1)
    rw [Sodd_bil] at this
    simpa [Pi.single_apply] using this
  · have := hx (Pi.single (.inl j) 1)
    rw [Sodd_bil] at this
    simpa [Pi.single_apply] using this
  · have := hx (Pi.single (.inr (.inr ())) 1)
    rw [Sodd_bil] at this
    have h3 : 2 * x (.inr (.inr ())) = 0 := by simpa [Pi.single_apply] using this
    have := (mul_eq_zero.mp h3).resolve_left h2
    simpa using this

theorem Sodd_quad (h2 : (2 : K) ≠ 0) (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    StatedQuadOdd n K v = 2⁻¹ * (v ⬝ᵥ Sodd n K *ᵥ v) := by
  rw [Sodd_bil, StatedQuadOdd]
  have : ∑ i, (v (.inl i) * v (.inr (.inl i)) + v (.inr (.inl i)) * v (.inl i)) =
      2 * ∑ i, v (.inl i) * v (.inr (.inl i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  field_simp

end Odd

section Minus

variable (n : ℕ) (K : Type) [Field K] (b c : K)

@[expose] noncomputable def Sminus :
    Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K :=
  Matrix.of fun i j =>
  match i, j with
  | .inl a, .inr (.inl b') => if a = b' then 1 else 0
  | .inr (.inl a), .inl b' => if a = b' then 1 else 0
  | .inr (.inr i), .inr (.inr j) => !![2, b; b, 2 * c] i j
  | _, _ => 0

theorem Sminus_bil (v w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    v ⬝ᵥ Sminus n K b c *ᵥ w =
      ∑ i, (v (.inl i) * w (.inr (.inl i)) + v (.inr (.inl i)) * w (.inl i)) +
      (2 * (v (.inr (.inr 0)) * w (.inr (.inr 0))) +
        b * (v (.inr (.inr 0)) * w (.inr (.inr 1)) + v (.inr (.inr 1)) * w (.inr (.inr 0))) +
        2 * c * (v (.inr (.inr 1)) * w (.inr (.inr 1)))) := by
  simp [Sminus, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Finset.sum_add_distrib,
    Fin.sum_univ_two]
  ring

theorem Sminus_symm (v w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    v ⬝ᵥ Sminus n K b c *ᵥ w = w ⬝ᵥ Sminus n K b c *ᵥ v := by
  rw [Sminus_bil, Sminus_bil]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

theorem Sminus_nd (h2 : (2 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (hx : ∀ y, x ⬝ᵥ Sminus n K b c *ᵥ y = 0) : x = 0 := by
  have hdet : 4 * c - b ^ 2 ≠ 0 := by
    intro h
    apply hbc (-b / 2)
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have : (-b / 2) ^ 2 + b * (-b / 2) + c = (4 * c - b ^ 2) / 4 := by
      field_simp
      ring
    rw [this, h]
    simp
  have e0 := hx (Pi.single (.inr (.inr 0)) 1)
  have e1 := hx (Pi.single (.inr (.inr 1)) 1)
  rw [Sminus_bil] at e0 e1
  simp at e0 e1
  have hx0 : x (.inr (.inr 0)) = 0 := by
    apply (mul_eq_zero.mp (show (4 * c - b ^ 2) * x (.inr (.inr 0)) = 0 by
      linear_combination (2 * c) * e0 - b * e1)).resolve_left hdet
  have hx1 : x (.inr (.inr 1)) = 0 := by
    apply (mul_eq_zero.mp (show (4 * c - b ^ 2) * x (.inr (.inr 1)) = 0 by
      linear_combination (2 : K) * e1 - b * e0 + (b * 0) * e0)).resolve_left hdet
  funext i
  rcases i with j | j | j
  · have := hx (Pi.single (.inr (.inl j)) 1)
    rw [Sminus_bil] at this
    simpa [Pi.single_apply] using this
  · have := hx (Pi.single (.inl j) 1)
    rw [Sminus_bil] at this
    simpa [Pi.single_apply] using this
  · fin_cases j
    · simpa using hx0
    · simpa using hx1

theorem Sminus_quad (h2 : (2 : K) ≠ 0) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c v = 2⁻¹ * (v ⬝ᵥ Sminus n K b c *ᵥ v) := by
  rw [Sminus_bil, StatedQuadMinus]
  have : ∑ i, (v (.inl i) * v (.inr (.inl i)) + v (.inr (.inl i)) * v (.inl i)) =
      2 * ∑ i, v (.inl i) * v (.inr (.inl i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  field_simp
  ring

end Minus

section Models

variable {K : Type} [Field K] [Finite K] [CharP K 5]

omit [Finite K] in
theorem two_ne_zero_of_char_five : (2 : K) ≠ 0 := by
  intro h
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have h1 : (1 : K) = 0 := by linear_combination h5 - 2 * h
  exact one_ne_zero h1

theorem pomegaPlus_involution {n : ℕ} (hn : 4 ≤ n)
    (z : StatedProj (StatedOmega (StatedQuadPlus n K))) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    (∃ Φ : C55 →* StatedProj (StatedOmega (StatedQuadPlus n K)), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹) ∨
    (∃ X Y : StatedProj (StatedOmega (StatedQuadPlus n K)), X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧
      Commute ⁅Y, X⁆ X ∧ Commute ⁅Y, X⁆ Y ∧ ⁅Y, X⁆ ≠ 1 ∧ z * X * z⁻¹ = X⁻¹) :=
  orth_involution (Splus n K) (Splus_symm n K) (Splus_nd n K)
    (Splus_quad n K two_ne_zero_of_char_five)
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) z hz1 hz2

theorem pomegaOdd_involution {n : ℕ} (hn : 3 ≤ n)
    (z : StatedProj (StatedOmega (StatedQuadOdd n K))) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    (∃ Φ : C55 →* StatedProj (StatedOmega (StatedQuadOdd n K)), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹) ∨
    (∃ X Y : StatedProj (StatedOmega (StatedQuadOdd n K)), X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧
      Commute ⁅Y, X⁆ X ∧ Commute ⁅Y, X⁆ Y ∧ ⁅Y, X⁆ ≠ 1 ∧ z * X * z⁻¹ = X⁻¹) :=
  orth_involution (Sodd n K) (Sodd_symm n K) (Sodd_nd n K two_ne_zero_of_char_five)
    (Sodd_quad n K two_ne_zero_of_char_five)
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega) z hz1 hz2

theorem pomegaMinus_involution {n : ℕ} (hn : 4 ≤ n) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (z : StatedProj (StatedOmega (StatedQuadMinus n K b c))) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    (∃ Φ : C55 →* StatedProj (StatedOmega (StatedQuadMinus n K b c)), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹) ∨
    (∃ X Y : StatedProj (StatedOmega (StatedQuadMinus n K b c)), X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧
      Commute ⁅Y, X⁆ X ∧ Commute ⁅Y, X⁆ Y ∧ ⁅Y, X⁆ ≠ 1 ∧ z * X * z⁻¹ = X⁻¹) :=
  orth_involution (Sminus n K b c) (Sminus_symm n K b c)
    (Sminus_nd n K b c two_ne_zero_of_char_five hbc)
    (Sminus_quad n K b c two_ne_zero_of_char_five)
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) z hz1 hz2

end Models

end CFSG.HardMathSupport.Foote.ModuleExclusions
