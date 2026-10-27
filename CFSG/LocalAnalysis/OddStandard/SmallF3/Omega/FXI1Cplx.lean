module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXI1Lin
public import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

private theorem fx_even_of_sq_neg_one {M : Type*} [AddCommGroup M] [Module (ZMod 3) M]
    [FiniteDimensional (ZMod 3) M] (g : Module.End (ZMod 3) M) (hg : g * g = -1) :
    Even (Module.finrank (ZMod 3) M) := by
  have hsq : ∀ y : ZMod 3, y * y ≠ -1 := by decide
  have hneg : (-1 : Module.End (ZMod 3) M) = (-1 : ZMod 3) • (1 : Module.End (ZMod 3) M) := by
    simp
  have hdet : LinearMap.det g * LinearMap.det g = (-1) ^ Module.finrank (ZMod 3) M := by
    have h := congrArg LinearMap.det hg
    rw [Module.End.mul_eq_comp, LinearMap.det_comp, hneg, LinearMap.det_smul,
      Module.End.one_eq_id, LinearMap.det_id, mul_one] at h
    exact h
  rcases Nat.even_or_odd (Module.finrank (ZMod 3) M) with he | ho
  · exact he
  · exfalso
    have hodd : (-1 : ZMod 3) ^ Module.finrank (ZMod 3) M = -1 := ho.neg_one_pow
    rw [hodd] at hdet
    exact hsq _ hdet

theorem fx_even_finrank_of_sq_neg_one (g : Module.End (ZMod 3) V) (hg : g * g = -1)
    {W : Submodule (ZMod 3) V} (hW : ∀ w ∈ W, g w ∈ W) :
    Even (Module.finrank (ZMod 3) W) := by
  have hf : (g.restrict hW) * (g.restrict hW) = -1 := by
    ext w
    have h := congrArg (fun e : Module.End (ZMod 3) V => e (w : V)) hg
    simpa [Module.End.mul_apply] using h
  exact fx_even_of_sq_neg_one (g.restrict hW) hf

theorem fx_step5 (hdim : Module.finrank (ZMod 3) V = 6) {g U : Module.End (ZMod 3) V}
    (hg : g * g = -1) (hgU : g * U = U * g) (hU9 : U ^ 9 = 1) (hU3 : U ^ 3 ≠ 1) : False := by
  let N : Module.End (ZMod 3) V := U - 1
  have hN9 : N ^ 9 = 0 := by simpa [N] using fx_sub_one_pow_nine U hU9
  have hN3 : N ^ 3 ≠ 0 := by
    have h : N ^ 3 = U ^ 3 - 1 := by simpa [N] using fx_sub_one_pow_three U
    rw [h]
    exact sub_ne_zero.mpr hU3
  have hgN : g * N = N * g := by
    change g * (U - 1) = (U - 1) * g
    rw [mul_sub, sub_mul, mul_one, one_mul, hgU]
  let K : ℕ → Submodule (ZMod 3) V := fun i => LinearMap.ker (N ^ i)
  have hKinv : ∀ i, ∀ w ∈ K i, g w ∈ K i := by
    intro i w hw
    have hcomm : Commute g (N ^ i) := (show Commute g N from hgN).pow_right i
    have hgw : (N ^ i) (g w) = g ((N ^ i) w) := by
      have h := congrArg (fun e : Module.End (ZMod 3) V => e w) hcomm.eq
      simpa [Module.End.mul_apply] using h.symm
    change (N ^ i) w = 0 at hw
    change (N ^ i) (g w) = 0
    rw [hgw, hw, map_zero]
  have hlt : ∀ i ≤ 3, K i < K (i + 1) := by
    intro i hi
    refine lt_of_le_of_ne ?_ ?_
    · show LinearMap.ker (N ^ i) ≤ LinearMap.ker (N ^ (i + 1))
      rw [pow_succ']
      simpa [Module.End.mul_eq_comp] using LinearMap.ker_le_ker_comp (N ^ i) N
    · intro heq
      have hconst := Module.End.ker_pow_constant (f := N) (k := i) heq 9
      have hzero : N ^ (i + 9) = 0 := by rw [pow_add, hN9, mul_zero]
      have htop : LinearMap.ker (N ^ i) = ⊤ := by rw [hconst, hzero, LinearMap.ker_zero]
      have hNi : N ^ i = 0 := LinearMap.ker_eq_top.mp htop
      have h3 : N ^ 3 = 0 := by
        have hpow : N ^ (3 - i) * N ^ i = N ^ 3 := by
          rw [← pow_add, Nat.sub_add_cancel hi]
        rw [← hpow, hNi, mul_zero]
      exact hN3 h3
  have heven : ∀ i, Even (Module.finrank (ZMod 3) (K i)) :=
    fun i => fx_even_finrank_of_sq_neg_one g hg (hKinv i)
  have hd0 : Module.finrank (ZMod 3) (K 0) = 0 := by
    show Module.finrank (ZMod 3) (LinearMap.ker (N ^ 0)) = 0
    simp [pow_zero, Module.End.one_eq_id, LinearMap.ker_id]
  have hdlt : ∀ i ≤ 3,
      Module.finrank (ZMod 3) (K i) < Module.finrank (ZMod 3) (K (i + 1)) :=
    fun i hi => Submodule.finrank_lt_finrank_of_lt (hlt i hi)
  have hd4le : Module.finrank (ZMod 3) (K 4) ≤ 6 := by
    have h := Submodule.finrank_le (K 4)
    rw [hdim] at h
    exact h
  obtain ⟨m1, hm1⟩ := heven 1
  obtain ⟨m2, hm2⟩ := heven 2
  obtain ⟨m3, hm3⟩ := heven 3
  obtain ⟨m4, hm4⟩ := heven 4
  have h01 : Module.finrank (ZMod 3) (K 0) < Module.finrank (ZMod 3) (K 1) :=
    hdlt 0 (by norm_num)
  have h12 : Module.finrank (ZMod 3) (K 1) < Module.finrank (ZMod 3) (K 2) :=
    hdlt 1 (by norm_num)
  have h23 : Module.finrank (ZMod 3) (K 2) < Module.finrank (ZMod 3) (K 3) :=
    hdlt 2 (by norm_num)
  have h34 : Module.finrank (ZMod 3) (K 3) < Module.finrank (ZMod 3) (K 4) :=
    hdlt 3 (by norm_num)
  omega

end CFSG.OddStandard.SmallF3.Omega
