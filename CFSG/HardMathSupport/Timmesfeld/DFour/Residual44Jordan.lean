module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Eigenspace.Zero

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Rank

variable [FiniteDimensional K V]

theorem finrank_map_add_finrank_inf_ker (f : V →ₗ[K] V) (W : Submodule K V) :
    finrank K (W.map f) + finrank K (W ⊓ ker f : Submodule K V) = finrank K W := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict W)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem finrank_range_pow_eq (z : Module.End K V) (k : ℕ) :
    finrank K (range (z ^ k)) = finrank K (range (z ^ (k + 1))) +
      finrank K (range (z ^ k) ⊓ ker z : Submodule K V) := by
  have h := finrank_map_add_finrank_inf_ker z (range (z ^ k))
  rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
  omega

theorem finrank_range_pow_succ_inf_le (z : Module.End K V) (k : ℕ) :
    finrank K (range (z ^ (k + 1)) ⊓ ker z : Submodule K V) ≤
      finrank K (range (z ^ k) ⊓ ker z : Submodule K V) := by
  refine Submodule.finrank_mono (inf_le_inf_right _ ?_)
  rw [pow_succ, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _

end Rank

section Skew

variable {Q : QuadraticForm K V} {z : Module.End K V}

theorem polar_pow_left (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y)) (k : ℕ) (x y : V) :
    polar Q ((z ^ k) x) y = (-1) ^ k * polar Q x ((z ^ k) y) := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    have e1 : (z ^ (k + 1)) x = (z ^ k) (z x) := by rw [pow_succ, Module.End.mul_apply]
    have e2 : (z ^ (k + 1)) y = z ((z ^ k) y) := by rw [pow_succ', Module.End.mul_apply]
    rw [e1, e2, ih, hz, pow_succ]
    ring

theorem polar_pow_self_odd (h2 : (2 : K) ≠ 0) (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y))
    {k : ℕ} (hk : Odd k) (x : V) : polar Q x ((z ^ k) x) = 0 := by
  have h := polar_pow_left hz k x x
  rw [polar_comm, hk.neg_one_pow] at h
  have h' : (2 : K) * polar Q x ((z ^ k) x) = 0 := by linear_combination h
  exact (mul_eq_zero.1 h').resolve_left h2

theorem finrank_range_pow_ne_one (h2 : (2 : K) ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y)) {k : ℕ} (hk : Odd k) :
    finrank K (range (z ^ k)) ≠ 1 := by
  intro h1
  obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 w.2
  apply hw0
  apply Subtype.ext
  change (w : V) = 0
  refine hnd.1 (w : V) fun y => ?_
  change polar Q (w : V) y = 0
  obtain ⟨c, hc⟩ := hw ⟨(z ^ k) y, LinearMap.mem_range_self _ y⟩
  have hc' : c • (w : V) = (z ^ k) y := congrArg Subtype.val hc
  rw [← hx, polar_pow_left hz, ← hc', polar_smul_right, ← hx, polar_pow_self_odd h2 hz hk,
    smul_zero, mul_zero]

end Skew

section Jordan

variable [FiniteDimensional K V] {Q : QuadraticForm K V} {z : Module.End K V}

theorem jordan_four_four (h2 : (2 : K) ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    (hV : finrank K V = 8) (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y))
    (hnil : IsNilpotent z) (hY : ∀ w, z (z w) = 0 → Q w = 0) :
    z ^ 4 = 0 ∧ finrank K (ker z) = 2 ∧ finrank K (ker (z ^ 2)) = 4 ∧
      ker z ≤ range (z ^ 3) := by
  have h8 : z ^ 8 = 0 := by
    have h := LinearMap.aeval_self_charpoly z
    rw [hnil.charpoly_eq_X_pow_finrank, hV, map_pow, Polynomial.aeval_X] at h
    exact h
  have hsq : ∀ w, (z ^ 2) w = z (z w) := fun w => by
    rw [pow_two, Module.End.mul_apply]
  have hiso : ∀ w ∈ ker (z ^ 2), ∀ w' ∈ ker (z ^ 2), polar Q w w' = 0 := by
    intro w hw w' hw'
    rw [LinearMap.mem_ker, hsq] at hw hw'
    have hww : z (z (w + w')) = 0 := by rw [map_add, map_add, hw, hw', add_zero]
    rw [polar, hY _ hww, hY _ hw, hY _ hw', sub_zero, sub_zero]
  have hperp : range (z ^ 2) = LinearMap.BilinForm.orthogonal (polarBilin Q) (ker (z ^ 2)) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      change polar Q y ((z ^ 2) x) = 0
      rw [polar_comm, polar_pow_left hz, LinearMap.mem_ker.1 hy]
      simp
    · have hn := LinearMap.finrank_range_add_finrank_ker (z ^ 2 : Module.End K V)
      rw [LinearMap.BilinForm.finrank_orthogonal hnd]
      omega
  have hYle : ker (z ^ 2) ≤ range (z ^ 2) := by
    intro w hw
    rw [hperp, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hiso y hy w hw
  have hker12 : ker z ≤ ker (z ^ 2) := fun w hw => by
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hsq, hw, map_zero]
  have hr := finrank_range_pow_eq z
  have ha := finrank_range_pow_succ_inf_le z
  have hr0 : finrank K (range (z ^ 0)) = 8 := by
    rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, finrank_top, hV]
  have ha0 : finrank K (range (z ^ 0) ⊓ ker z : Submodule K V) = finrank K (ker z) := by
    rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, top_inf_eq]
  have ha2 : finrank K (range (z ^ 2) ⊓ ker z : Submodule K V) = finrank K (ker z) := by
    rw [inf_eq_right.2 (hker12.trans hYle)]
  have hr8 : finrank K (range (z ^ 8)) = 0 := by
    rw [h8, LinearMap.range_zero, finrank_bot]
  have hn1 := LinearMap.finrank_range_add_finrank_ker z
  have hn2 := LinearMap.finrank_range_add_finrank_ker (z ^ 2)
  have hr4 : finrank K (range (z ^ 4)) + finrank K (ker (z ^ 2)) =
      finrank K (range (z ^ 2)) := by
    have h := finrank_map_add_finrank_inf_ker (z ^ 2) (range (z ^ 2))
    rw [← LinearMap.range_comp, ← Module.End.mul_eq_comp, ← pow_add,
      inf_eq_right.2 hYle] at h
    exact h
  have e0 := hr 0
  have e1 := hr 1
  have e2 := hr 2
  have e3 := hr 3
  have e4 := hr 4
  have e5 := hr 5
  have e6 := hr 6
  have e7 := hr 7
  have i0 := ha 0
  have i1 := ha 1
  have i2 := ha 2
  have i3 := ha 3
  have i4 := ha 4
  have i5 := ha 5
  have i6 := ha 6
  simp only [Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 e6 e7 i0 i1 i2 i3 i4 i5 i6
  rw [hV] at hn1 hn2
  have hd1 : finrank K (ker z) ≠ 1 := by
    intro h1
    have h7 : finrank K (range (z ^ 7)) = 1 := by omega
    exact finrank_range_pow_ne_one h2 hnd hz (by decide : Odd 7) h7
  have hd : finrank K (ker z) = 2 := by omega
  have hr4' : finrank K (range (z ^ 4)) = 0 := by omega
  have hz4 : z ^ 4 = 0 := LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 hr4')
  refine ⟨hz4, hd, by omega, ?_⟩
  have hle : range (z ^ 3) ≤ ker z := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', hz4, LinearMap.zero_apply]
  have heq : range (z ^ 3) = ker z := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [heq]

end Jordan

end CFSG.HardMathSupport.Timmesfeld.DFour
