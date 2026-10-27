module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3BabySylow
import CFSG.Monster.B.Pinned.Primes.ThreeRelations
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.BabySyl

open CFSG.Monster.B.Pinned Subgroup Module
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem finrank_add_le
    {W W' : Submodule (ZMod 3) (Fin 8 → ZMod 3)} (h : W' ≤ (Matrix.toBilin' MThree).orthogonal W) :
    finrank (ZMod 3) W + finrank (ZMod 3) W' ≤ 8 := by
  have hnd := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' MThree
    isUnit_det_MThree.ne_zero
  have h1 := Submodule.finrank_mono h
  have h2 := Submodule.finrank_le W
  rw [LinearMap.BilinForm.finrank_orthogonal hnd, Module.finrank_fin_fun] at h1
  rw [Module.finrank_fin_fun] at h2
  omega

private theorem exists_row {A : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : (A - 1) * (A - 1) ≠ 0) :
    ∃ i, (Pi.single i 1 ᵥ* A - Pi.single i 1) ᵥ* A ≠ Pi.single i 1 ᵥ* A - Pi.single i 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hA
  refine ⟨i, fun h => hi ?_⟩
  have e := Matrix.single_one_vecMul i ((A - 1) * (A - 1))
  rw [← Matrix.vecMul_vecMul] at e
  simp only [Matrix.vecMul_sub, Matrix.vecMul_one, h, sub_self] at e
  exact e.symm

private theorem finrank_le_three
    {W : Submodule (ZMod 3) (Fin 8 → ZMod 3)} (hiso : W ≤ (Matrix.toBilin' MThree).orthogonal W)
    {A : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hA : ∀ u v : Fin 8 → ZMod 3, (u ᵥ* A) ⬝ᵥ (MThree *ᵥ (v ᵥ* A)) = u ⬝ᵥ (MThree *ᵥ v))
    (hfix : ∀ u ∈ W, u ᵥ* A = u) (hA1 : (A - 1) * (A - 1) ≠ 0) : finrank (ZMod 3) W ≤ 3 := by
  obtain ⟨i, hi⟩ := exists_row hA1
  have hto : Pi.single i 1 ᵥ* A - Pi.single i 1 ∈ (Matrix.toBilin' MThree).orthogonal W := by
    refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun w hw => ?_
    have hw' := hA w (Pi.single i 1)
    rw [hfix w hw] at hw'
    rw [Matrix.toBilin'_apply', Matrix.mulVec_sub, dotProduct_sub, hw', sub_self]
  have hlt : W < W ⊔ Submodule.span (ZMod 3) {Pi.single i 1 ᵥ* A - Pi.single i 1} :=
    SetLike.lt_iff_le_and_exists.2 ⟨le_sup_left, _,
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), fun h => hi (hfix _ h)⟩
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := finrank_add_le (sup_le hiso (Submodule.span_le.2 (Set.singleton_subset_iff.2 hto)))
  omega

theorem card_mul_le_of_le_sylS
    {D : Subgroup (GL (Fin 8) (ZMod 3))} (hDS : D ≤ sylS)
    (hD : ∀ d ∈ D, ∀ d' ∈ D, d * d' = d' * d) {W : Submodule (ZMod 3) (Fin 8 → ZMod 3)}
    (hiso : W ≤ (Matrix.toBilin' MThree).orthogonal W)
    (hfix : ∀ d ∈ D, ∀ u ∈ W, u ᵥ* (d : Matrix (Fin 8) (Fin 8) (ZMod 3)) = u) :
    3 ^ finrank (ZMod 3) W * Nat.card D ≤ 3 ^ 5 := by
  have h4 := finrank_add_le hiso
  have hdvd : Nat.card D ∣ 3 ^ 4 := by
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num, ← card_sylS]; exact card_dvd_of_le hDS
  obtain ⟨m, hm, hDm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rcases (by omega : m ≤ 1 ∨ m = 2 ∨ 3 ≤ m) with hm1 | rfl | hm3
  · rw [hDm]
    calc 3 ^ finrank (ZMod 3) W * 3 ^ m ≤ 3 ^ 4 * 3 ^ 1 :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
            (Nat.pow_le_pow_right (by norm_num) hm1)
      _ = 3 ^ 5 := by norm_num
  · obtain ⟨d, hd, hd1⟩ : ∃ d ∈ D, ((d : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) *
        ((d : Matrix (Fin 8) (Fin 8) (ZMod 3)) - 1) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h7 : Nat.card D ≤ 7 :=
        card_le_seven (S := (D : Set _)) (fun s hs => exists_eq_of_mem_sylS (hDS hs)) hcon
      rw [hDm] at h7
      norm_num at h7
    rw [hDm]
    calc 3 ^ finrank (ZMod 3) W * 3 ^ 2 ≤ 3 ^ 3 * 3 ^ 2 := Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by norm_num) (finrank_le_three hiso
            (isometry_of_mem_sylS (hDS hd)) (hfix d hd) hd1))
      _ = 3 ^ 5 := by norm_num
  · obtain ⟨ha, hb, hc, h27⟩ := gens_mem_of_le_sylS hDS hD (by
      rw [hDm]; exact (Nat.pow_le_pow_right (by norm_num) hm3 : 3 ^ 3 ≤ 3 ^ m))
    have hW : W ≤ Submodule.span (ZMod 3) {![0, 2, 2, 1, 0, 1, 1, 0]} := fun u hu => by
      obtain ⟨r, hr⟩ := eq_smul_of_fix (hfix _ ha u hu) (hfix _ hb u hu) (hfix _ hc u hu)
      exact Submodule.mem_span_singleton.2 ⟨r, hr.symm⟩
    have h1 := (Submodule.finrank_mono hW).trans_eq (finrank_span_singleton (by decide))
    rw [h27]
    calc 3 ^ finrank (ZMod 3) W * 27 ≤ 3 ^ 1 * 27 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h1)
      _ ≤ 3 ^ 5 := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.BabySyl

end
