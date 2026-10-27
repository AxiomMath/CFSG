module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HU7

open Matrix CFSG.LocalAnalysis.GLTheoremA.Y10GNegCore

variable {F : Type} [Field F] [CharP F 2]

@[expose] def herm2 (u v : Fin 6 → F) : F := ∑ i, u i ^ 2 * v i

theorem sq_add_two (a b : F) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have h := add_pow_char (p := 2) a b
  simpa using h

theorem sq_sum_two {ι : Type} (s : Finset ι) (f : ι → F) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sq_add_two, ih]

theorem herm2_add_left (u u' v : Fin 6 → F) : herm2 (u + u') v = herm2 u v + herm2 u' v := by
  unfold herm2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  rw [sq_add_two]
  ring

theorem herm2_smul_left (c : F) (u v : Fin 6 → F) : herm2 (c • u) v = c ^ 2 * herm2 u v := by
  unfold herm2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem herm2_add_right (u v v' : Fin 6 → F) : herm2 u (v + v') = herm2 u v + herm2 u v' := by
  unfold herm2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

theorem herm2_smul_right (c : F) (u v : Fin 6 → F) : herm2 u (c • v) = c * herm2 u v := by
  unfold herm2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem herm2_zero_left (v : Fin 6 → F) : herm2 0 v = 0 := by
  unfold herm2
  simp

theorem herm2_zero_right (u : Fin 6 → F) : herm2 u 0 = 0 := by
  unfold herm2
  simp

theorem herm2_sum_left {ι : Type} (s : Finset ι) (u : ι → Fin 6 → F) (v : Fin 6 → F) :
    herm2 (∑ i ∈ s, u i) v = ∑ i ∈ s, herm2 (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm2_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm2_add_left, ih]

theorem herm2_sum_right {ι : Type} (s : Finset ι) (u : Fin 6 → F) (v : ι → Fin 6 → F) :
    herm2 u (∑ i ∈ s, v i) = ∑ i ∈ s, herm2 u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm2_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm2_add_right, ih]

theorem herm2_unitary {g : Matrix (Fin 6) (Fin 6) F}
    (hU : (g.map (fun x : F => x ^ 2))ᵀ * g = 1) (u v : Fin 6 → F) :
    herm2 (g *ᵥ u) (g *ᵥ v) = herm2 u v := by
  have hcol : ∀ k l : Fin 6, ∑ i, (g i k) ^ 2 * g i l = if k = l then 1 else 0 := by
    intro k l
    have h := congrFun (congrFun hU k) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.transpose_apply, Matrix.map_apply] using h
  have step1 : ∀ i : Fin 6, (∑ k, g i k * u k) ^ 2 * ∑ l, g i l * v l =
      ∑ k, ∑ l, (g i k) ^ 2 * (u k) ^ 2 * (g i l * v l) := by
    intro i
    rw [sq_sum_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow]
  have step2 : ∀ k l : Fin 6, ∑ i, (g i k) ^ 2 * (u k) ^ 2 * (g i l * v l) =
      (u k) ^ 2 * v l * (if k = l then 1 else 0) := by
    intro k l
    rw [← hcol k l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold herm2
  simp only [mulVec, dotProduct]
  simp only [step1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp only [step2, mul_ite, mul_one, mul_zero]
  simp

theorem herm2_adj_one {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm2 (Y *ᵥ a) (Y *ᵥ b) = herm2 a b) (hY7 : Y ^ 7 = 1) (a b : Fin 6 → F) :
    herm2 (Y *ᵥ a) b = herm2 a ((Y ^ 6) *ᵥ b) := by
  have hinv : Y * Y ^ 6 = 1 := by
    rw [← pow_succ']
    exact hY7
  have h : Y *ᵥ ((Y ^ 6) *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  calc herm2 (Y *ᵥ a) b = herm2 (Y *ᵥ a) (Y *ᵥ ((Y ^ 6) *ᵥ b)) := by rw [h]
    _ = herm2 a ((Y ^ 6) *ᵥ b) := hY _ _

theorem herm2_adj_pow {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm2 (Y *ᵥ a) (Y *ᵥ b) = herm2 a b) (hY7 : Y ^ 7 = 1) (k : ℕ)
    (a b : Fin 6 → F) : herm2 ((Y ^ k) *ᵥ a) b = herm2 a (((Y ^ 6) ^ k) *ᵥ b) := by
  induction k generalizing a b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, herm2_adj_one hY hY7, ih, pow_succ (Y ^ 6) k,
      ← Matrix.mulVec_mulVec]

theorem herm2_adj_f {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm2 (Y *ᵥ a) (Y *ᵥ b) = herm2 a b) (hY7 : Y ^ 7 = 1) (u v : Fin 6 → F) :
    herm2 ((Y ^ 3 + Y + 1) *ᵥ u) v = herm2 u (((Y ^ 6) ^ 3 + Y ^ 6 + 1) *ᵥ v) := by
  have h3 := herm2_adj_pow hY hY7 3 u v
  have h1 := herm2_adj_pow hY hY7 1 u v
  rw [pow_one, pow_one] at h1
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, herm2_add_left, herm2_add_right, h3, h1]

theorem herm2_iso_f {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm2 (Y *ᵥ a) (Y *ᵥ b) = herm2 a b) (hY7 : Y ^ 7 = 1)
    {u u' : Fin 6 → F} (hu : (Y ^ 3 + Y + 1) *ᵥ u = 0) (hu' : (Y ^ 3 + Y + 1) *ᵥ u' = 0) :
    herm2 u u' = 0 := by
  have hM := matI2 (Z := Y) hY7
  have hv : ((Y ^ 6) ^ 3 + Y ^ 6 + 1) *ᵥ ((Y ^ 3 * (Y + 1)) *ᵥ u') = u' := by
    rw [Matrix.mulVec_mulVec, hM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hu',
      Matrix.mulVec_zero, add_zero]
  calc herm2 u u' = herm2 u (((Y ^ 6) ^ 3 + Y ^ 6 + 1) *ᵥ ((Y ^ 3 * (Y + 1)) *ᵥ u')) := by rw [hv]
    _ = herm2 ((Y ^ 3 + Y + 1) *ᵥ u) ((Y ^ 3 * (Y + 1)) *ᵥ u') := (herm2_adj_f hY hY7 _ _).symm
    _ = 0 := by rw [hu, herm2_zero_left]

theorem root_free_two (hF4 : ∀ x : F, x ^ 4 = x) (x : F) : x ^ 3 + x + 1 ≠ 0 := by
  intro h
  have h3 : x ^ 3 = x + 1 := by linear_combination h - (x + 1) * (two_eq_zero' (F := F))
  have h4 : x ^ 4 = x ^ 2 + x := by linear_combination x * h3
  have hx2 : x ^ 2 = 0 := by linear_combination hF4 x - h4
  have hx : x = 0 := (pow_eq_zero_iff two_ne_zero).1 hx2
  subst hx
  norm_num at h

end CFSG.LocalAnalysis.GLTheoremA.HU7

end
