module

public import CFSG.GH74.GLS.Stage4.HexCK6

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem root6_norm (hC : Hex6Comm root) {y : G} (hy : y ∈ root 6) {n : G}
    (hn : n ∈ Vsub root 2 4) : y * n * y⁻¹ ∈ Vsub root 2 4 := by
  have key : root 6 ≤ Subgroup.normalizer ((Vsub root 2 4 : Subgroup G) : Set G) := by
    refine le_normalizer_iSup₂ (A := root 6) (P := {k | k ∈ intList 2 4}) (X := root)
      (fun x hx γ hγ z hz => ?_)
    have hγ' := mem_intList_iff.1 hγ
    have hcase : γ = 2 ∨ γ = 3 ∨ γ = 4 := by omega
    rcases hcase with rfl | rfl | rfl
    · have h1 : ⁅z, x⁆ ∈ root 4 := hC.l26 z hz x hx
      have e : x * z * x⁻¹ = (⁅z, x⁆)⁻¹ * z := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (root_le_Vsub (by norm_num) (by norm_num) h1))
        (root_le_Vsub (by norm_num) (by norm_num) hz)
    · have : x * z * x⁻¹ = z := by
        rw [mul_inv_eq_iff_eq_mul]; exact (hC.o36 z hz x hx).symm
      rw [this]; exact root_le_Vsub (by norm_num) (by norm_num) hz
    · have : x * z * x⁻¹ = z := by
        rw [mul_inv_eq_iff_eq_mul]; exact (hC.l46 z hz x hx).symm
      rw [this]; exact root_le_Vsub (by norm_num) (by norm_num) hz
  exact (Subgroup.mem_normalizer_iff.1 (key hy) n).1 hn

theorem r2_mem_V24 (R : RGD2 6 H r₁ r₂ U root) {v : G} (hv : v ∈ Vsub root 2 4) :
    r₂ * v * r₂⁻¹ ∈ Vsub root 2 4 := by
  have := r2_mem_Vsub R (i := 2) (j := 4) (by norm_num) (by norm_num) hv
  norm_num at this; exact this

theorem r2_inv_mem_V24 (R : RGD2 6 H r₁ r₂ U root) {v : G} (hv : v ∈ Vsub root 2 4) :
    r₂⁻¹ * v * r₂ ∈ Vsub root 2 4 := by
  have := r2_inv_mem_Vsub R (i := 2) (j := 4) (by norm_num) (by norm_num) hv
  norm_num at this; exact this

theorem rootNeg6_norm (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) {z : G}
    (hz : z ∈ root (-6)) {n : G} (hn : n ∈ Vsub root 2 4) : z * n * z⁻¹ ∈ Vsub root 2 4 := by
  have h1 := root6_norm hC (r2_neg6_mem R hz) (r2_mem_V24 R hn)
  have h2 := r2_inv_mem_V24 R h1
  have e : r₂⁻¹ * (r₂ * z * r₂⁻¹ * (r₂ * n * r₂⁻¹) * (r₂ * z * r₂⁻¹)⁻¹) * r₂ = z * n * z⁻¹ := by
    group
  rwa [e] at h2

theorem root1_norm (R : RGD2 6 H r₁ r₂ U root) {x : G} (hx : x ∈ root 1) {n : G}
    (hn : n ∈ Vsub root 2 4) : x * n * x⁻¹ ∈ Vsub root 2 4 :=
  Vsub_norm_left R (by norm_num) (by norm_num) (by simpa using hx) hn

theorem root5_norm (R : RGD2 6 H r₁ r₂ U root) {x : G} (hx : x ∈ root 5) {n : G}
    (hn : n ∈ Vsub root 2 4) : x * n * x⁻¹ ∈ Vsub root 2 4 :=
  Vsub_norm_right R (by norm_num) (by norm_num) (by simpa using hx) hn

end CFSG.GH74.GLS.Stage4.Hex
