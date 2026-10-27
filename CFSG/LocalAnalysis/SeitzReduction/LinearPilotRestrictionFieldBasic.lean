module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

theorem eq_one_of_mem_radical_of_mem_scalars (i₀ : Fin n) {g : SpecialLinearGroup (Fin n) K}
    (hR : g ∈ P.radical K) (hZ : g ∈ scalars n K) : g = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hZ
  have h1 := hR i₀ i₀ le_rfl
  rw [hc, scalar_apply, diagonal_apply_eq, one_apply_eq] at h1
  ext i j
  rw [hc, scalar_apply, h1, diagonal_one]
  rfl

theorem slConjugation_transvection_mem_radical [CharP K 2] (B : GL (Fin n) K) {i j : Fin n}
    (hij : i ≠ j) (c : K)
    (h : conjAut n K B (proj n K (SpecialLinearGroup.transvection hij c)) ∈ P.radicalP K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B
      (SpecialLinearGroup.transvection hij c) ∈ P.radical K := by
  rw [conjAut_proj] at h
  obtain ⟨r, hr, hre⟩ := h
  set s := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B
    (SpecialLinearGroup.transvection hij c) with hsdef
  have hz : r⁻¹ * s ∈ scalars n K := proj_eq_proj_iff.1 hre
  set z := r⁻¹ * s with hzdef
  have hs : s = r * z := by rw [hzdef, mul_inv_cancel_left]
  have hzc : ∀ x, z * x = x * z := fun x =>
    (Subgroup.mem_center_iff.1 (scalars_le_center n K hz) x).symm
  have hss : s * s = 1 := by
    rw [hsdef, ← map_mul, transvection_mul_self, map_one]
  have hzz : z * z = (r * r)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    have hzr : z * r = r * z := hzc r
    calc z * z * (r * r) = z * (z * r) * r := by simp only [mul_assoc]
      _ = z * (r * z) * r := by rw [hzr]
      _ = (z * r) * (z * r) := by simp only [mul_assoc]
      _ = (r * z) * (r * z) := by rw [hzr]
      _ = 1 := by rw [← hs, hss]
  have hzzR : z * z ∈ P.radical K := by
    rw [hzz]
    exact inv_mem (mul_mem hr hr)
  have hzzZ : z * z ∈ scalars n K := mul_mem hz hz
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by subst h0; exact i.elim0
  have hz1 : z = 1 :=
    eq_one_of_mem_scalars_of_mul_self hz (P.eq_one_of_mem_radical_of_mem_scalars ⟨0, hn⟩ hzzR hzzZ)
  rw [hs, hz1, mul_one]
  exact hr

theorem conj_single_apply_eq_zero (B : GL (Fin n) K) {i j : Fin n} (hij : i ≠ j)
    (h : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B
      (SpecialLinearGroup.transvection hij 1) ∈ P.radical K) {a b : Fin n}
    (hab : P.level b ≤ P.level a) :
    ((B : Matrix (Fin n) (Fin n) K) * (single i j 1 : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) a b = 0 := by
  have h1 := h a b hab
  rw [coe_slConjugation, SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.add_apply] at h1
  exact add_eq_left.1 h1

theorem apply_eq_zero_of_level_two {B B' : Matrix (Fin n) (Fin n) K} (hBB' : B' * B = 1)
    (hB : ∀ i j, P.level i < P.level j → ∀ a b, P.level b ≤ P.level a →
      (B * (single i j 1 : Matrix (Fin n) (Fin n) K) * B') a b = 0)
    {a i j : Fin n} (ha : P.level a = 2) (hj : P.level j = 2) (hi : P.level i < 2) :
    B a i = 0 := by
  have h1 : B * (single i j 1 : Matrix (Fin n) (Fin n) K) =
      (B * (single i j 1 : Matrix (Fin n) (Fin n) K) * B') * B := by
    rw [Matrix.mul_assoc _ B', hBB', Matrix.mul_one]
  have h2 := congrFun (congrFun h1 a) j
  rw [mul_single_apply_same, mul_one, mul_apply] at h2
  rw [h2]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [hB i j (by omega) a l (by rw [ha]; exact P.level_le_two l), zero_mul]

theorem apply_eq_zero_of_level_zero {B B' : Matrix (Fin n) (Fin n) K} (hBB' : B * B' = 1)
    (hB' : ∀ i j, P.level i < P.level j → ∀ a b, P.level b ≤ P.level a →
      (B' * (single i j 1 : Matrix (Fin n) (Fin n) K) * B) a b = 0)
    {i a j : Fin n} (ha : P.level a = 0) (hj : P.level j = 0) (hi : 0 < P.level i) :
    B i a = 0 := by
  have h1 : (single j i 1 : Matrix (Fin n) (Fin n) K) * B =
      B * (B' * (single j i 1 : Matrix (Fin n) (Fin n) K) * B) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBB', Matrix.one_mul]
  have h2 := congrFun (congrFun h1 j) a
  rw [single_mul_apply_same, one_mul, mul_apply] at h2
  rw [h2]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [hB' j i (by omega) l a (by rw [ha]; exact Nat.zero_le _), mul_zero]

theorem blockTriangular_of_conj_single {B B' : Matrix (Fin n) (Fin n) K} (hBB' : B * B' = 1)
    (hB'B : B' * B = 1) (hk : 0 < k)
    (hB : ∀ i j, P.level i < P.level j → ∀ a b, P.level b ≤ P.level a →
      (B * (single i j 1 : Matrix (Fin n) (Fin n) K) * B') a b = 0)
    (hB' : ∀ i j, P.level i < P.level j → ∀ a b, P.level b ≤ P.level a →
      (B' * (single i j 1 : Matrix (Fin n) (Fin n) K) * B) a b = 0) :
    B.BlockTriangular P.level := by
  intro i j hij
  have hi2 := P.level_le_two i
  rcases (by omega : P.level j = 0 ∨ (P.level j = 1 ∧ P.level i = 2)) with hj0 | ⟨hj1, hi2'⟩
  · exact P.apply_eq_zero_of_level_zero hBB' hB' hj0 (P.level_u ⟨0, hk⟩) (by omega)
  · exact P.apply_eq_zero_of_level_two hB'B hB hi2' (P.level_w ⟨0, hk⟩) (by omega)

theorem blockTriangular_of_conjAut [CharP K 2] (hk : 0 < k) (B : GL (Fin n) K)
    (hB : ∀ x ∈ P.radicalP K, conjAut n K B x ∈ P.radicalP K)
    (hB' : ∀ x ∈ P.radicalP K, conjAut n K B⁻¹ x ∈ P.radicalP K) :
    (B : Matrix (Fin n) (Fin n) K).BlockTriangular P.level := by
  have key : ∀ C : GL (Fin n) K, (∀ x ∈ P.radicalP K, conjAut n K C x ∈ P.radicalP K) →
      ∀ i j, P.level i < P.level j → ∀ a b, P.level b ≤ P.level a →
        ((C : Matrix (Fin n) (Fin n) K) * (single i j 1 : Matrix (Fin n) (Fin n) K) *
          ((C⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a b = 0 := by
    intro C hC i j hij a b hab
    have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
    refine P.conj_single_apply_eq_zero C hne ?_ hab
    exact P.slConjugation_transvection_mem_radical C hne 1
      (hC _ (Subgroup.mem_map_of_mem _ (P.transvection_mem_radical hne hij 1)))
  refine P.blockTriangular_of_conj_single (B' := ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    ?_ ?_ hk (key B hB) ?_
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  · intro i j hij a b hab
    have := key B⁻¹ hB' i j hij a b hab
    rwa [inv_inv] at this

end InvPlacement

end CFSG.SeitzReduction.LinearPilot
