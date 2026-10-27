module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

open CFSG.LocalAnalysis.GLTheoremA.CatB Module

@[expose] noncomputable def hermF (x y : Fin 6 → K4) : K4 := ∑ i, x i ^ 2 * y i

theorem hermF_smul_left (c : K4) (x y : Fin 6 → K4) : hermF (c • x) y = c ^ 2 * hermF x y := by
  unfold hermF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem hermF_smul_right (c : K4) (x y : Fin 6 → K4) : hermF x (c • y) = c * hermF x y := by
  unfold hermF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem hermF_add_right (x y z : Fin 6 → K4) : hermF x (y + z) = hermF x y + hermF x z := by
  unfold hermF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

theorem hermF_zero_right (x : Fin 6 → K4) : hermF x 0 = 0 := by
  unfold hermF
  simp

@[expose] noncomputable def perp (W : Submodule K4 (Fin 6 → K4)) : Submodule K4 (Fin 6 → K4) where
  carrier := {y | ∀ w ∈ W, hermF w y = 0}
  add_mem' := by
    intro y z hy hz w hw
    rw [hermF_add_right, hy w hw, hz w hw, add_zero]
  zero_mem' := by
    intro w _
    exact hermF_zero_right w
  smul_mem' := by
    intro c y hy w hw
    rw [hermF_smul_right, hy w hw, mul_zero]

theorem mem_perp {W : Submodule K4 (Fin 6 → K4)} {y : Fin 6 → K4} :
    y ∈ perp W ↔ ∀ w ∈ W, hermF w y = 0 := Iff.rfl

theorem K4_pow_four (c : K4) : c ^ 4 = c := by
  by_cases hc : c = 0
  · simp [hc]
  · have h3 := K4_pow_card_sub_one hc
    calc c ^ 4 = c ^ 3 * c := by ring
      _ = c := by rw [h3, one_mul]

theorem hermF_eq_zero_of_trace {w y : Fin 6 → K4}
    (h : ∀ c : K4, Algebra.trace (ZMod 2) K4 (hermF (c ^ 2 • w) y) = 0) : hermF w y = 0 := by
  apply trace_nondegenerate
  intro c
  have hc := h c
  rw [hermF_smul_left, show (c ^ 2) ^ 2 = c from by rw [← pow_mul]; exact K4_pow_four c] at hc
  rw [mul_comm]
  exact hc

theorem perp_restrict_eq_orth (W : Submodule K4 (Fin 6 → K4)) :
    (perp W).restrictScalars (ZMod 2) =
      (trForm 6).orthogonal (W.restrictScalars (ZMod 2)) := by
  ext y
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hy m hm
    have hy' : y ∈ perp W := (Submodule.restrictScalars_mem _ _ _).1 hy
    have hm' : m ∈ W := (Submodule.restrictScalars_mem _ _ _).1 hm
    have h0 : hermF m y = 0 := mem_perp.1 hy' m hm'
    show Algebra.trace (ZMod 2) K4 (hermF m y) = 0
    rw [h0, map_zero]
  · intro hy
    refine (Submodule.restrictScalars_mem _ _ _).2 (mem_perp.2 fun w hw => ?_)
    apply hermF_eq_zero_of_trace
    intro c
    have hm : c ^ 2 • w ∈ W := W.smul_mem _ hw
    have := hy (c ^ 2 • w) ((Submodule.restrictScalars_mem _ _ _).2 hm)
    exact this

theorem finrank_perp_add (W : Submodule K4 (Fin 6 → K4)) :
    Module.finrank K4 (perp W) + Module.finrank K4 W = 6 := by
  have hB := trForm_nondegenerate 6
  have h1 := LinearMap.BilinForm.finrank_orthogonal hB (W.restrictScalars (ZMod 2))
  rw [← perp_restrict_eq_orth] at h1
  have h2 : ∀ X : Submodule K4 (Fin 6 → K4),
      Module.finrank (ZMod 2) (X.restrictScalars (ZMod 2)) = 2 * Module.finrank K4 X := by
    intro X
    have h := Module.finrank_mul_finrank (ZMod 2) K4 X
    rw [finrank_K4] at h
    exact h.symm
  have h3 : Module.finrank (ZMod 2) (Fin 6 → K4) = 12 := by
    rw [finrank_pi_K4 6]
  have hW := Submodule.finrank_le (W.restrictScalars (ZMod 2))
  rw [h2, h3] at hW
  rw [h2, h2, h3] at h1
  omega

end CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

end
