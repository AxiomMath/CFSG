module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VMon
public import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.GorensteinWalter CFSG.ClassicalInvolution.Q3.TL4.MF163
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def sd (i : K) (hi : -1 = i * i) : SL(2, K) :=
  ⟨!![i, 0; 0, -i], by rw [Matrix.det_fin_two_of]; linear_combination hi⟩

@[expose] def sw : SL(2, K) :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

theorem coe_toGL_sd (i : K) (hi : -1 = i * i) :
    ((Matrix.SpecialLinearGroup.toGL (sd i hi) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![i, 0; 0, -i] := rfl

theorem coe_toGL_sw :
    ((Matrix.SpecialLinearGroup.toGL (sw : SL(2, K)) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] := rfl

theorem toPGL_sd (i : K) (hi : -1 = i * i) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (sd i hi) : PSL(2, K)) =
      Matrix.ProjGenLinGroup.mk (dm (-1)) := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  refine mk_eq_mk_of_smul (s := -i) (neg_ne_zero.mpr hi0) ?_
  ext a b
  rw [coe_toGL_sd, coe_dm]
  fin_cases a <;> fin_cases b <;> simp

theorem toPGL_sw :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (sw : SL(2, K)) : PSL(2, K)) =
      Matrix.ProjGenLinGroup.mk (dm (-1) * wm) := by
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  congr 1
  ext a b
  rw [coe_toGL_sw, Units.val_mul, coe_dm, coe_wm]
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem orderOf_mk_dm_neg_one (h2 : (2 : K) ≠ 0) :
    orderOf (Matrix.ProjGenLinGroup.mk (dm (-1 : Kˣ)) : PGL2 K) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_mul, ← dm_mul]
    have : (-1 : Kˣ) * (-1) = 1 := by simp
    rw [this, dm_one, map_one]
  · intro h
    rw [mk_eq_one_iff] at h
    obtain ⟨a, ha⟩ := h
    have e00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) ha
    have e11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) ha
    simp [coe_dm] at e00 e11
    exact h2 (by linear_combination e11 - e00)

theorem exists_conj_std [Finite K] {p f : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ f)
    (hp : Odd p) (hf : 0 < f) (hneg : IsSquare (-1 : K)) (h2 : (2 : K) ≠ 0) {z₀ : PGL2 K}
    (hz : z₀ ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, K) →* PGL2 K).range)
    (hz2 : orderOf z₀ = 2) :
    ∃ g : PSL(2, K), Matrix.ProjectiveSpecialLinearGroup.toPGL g * z₀ *
      (Matrix.ProjectiveSpecialLinearGroup.toPGL g)⁻¹ = Matrix.ProjGenLinGroup.mk (dm (-1)) := by
  obtain ⟨s, hs⟩ := hz
  obtain ⟨i, hi⟩ := hneg
  set s₀ : PSL(2, K) := QuotientGroup.mk (sd i hi) with hs₀def
  have hs₀ := toPGL_sd i hi
  have hord : orderOf s = 2 := by
    rw [← orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective s]
    rw [hs]; exact hz2
  have hord₀ : orderOf s₀ = 2 := by
    rw [← orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective s₀]
    rw [hs₀def, hs₀]; exact orderOf_mk_dm_neg_one h2
  obtain ⟨g, hg⟩ := isConj_iff.mp (CFSG.Walter.psl2_isConj_of_orderOf_eq_two K hK hp hf hord hord₀)
  refine ⟨g, ?_⟩
  have := congrArg (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, K) →* PGL2 K) hg
  rw [map_mul, map_mul, map_inv, hs, hs₀def, hs₀] at this
  exact this

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
