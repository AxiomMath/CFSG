module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] (h : UnitaryFieldData 3 1 F)

theorem gramForm_one_apply (u v : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u v = ∑ j, u j ^ 3 * v j := by
  rw [gramForm_apply, Matrix.one_mulVec]
  simp [dotProduct, bar_eq_cube h]

theorem gramForm_smul_left (c : F) (u v : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) (c • u) v =
      h.bar c * gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u v := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]

theorem gramForm_smul_right (c : F) (u v : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u (c • v) =
      c * gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u v := by
  rw [map_smul, smul_eq_mul]

theorem bar_gramForm (u v : Fin 3 → F) :
    h.bar (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u v) =
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v u :=
  (gramForm_one_isSymm h 3).eq u v

theorem eq_zero_of_gramForm_eq_zero {u : Fin 3 → F}
    (hu : ∀ y, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u y = 0) : u = 0 :=
  gramForm_one_separatingLeft h 3 u hu

include h in
theorem two_ne_zero' : (2 : F) ≠ 0 := by
  have := h.charP
  intro h2
  have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2
  rw [CharP.cast_eq_zero_iff F 3] at this
  omega

@[expose] noncomputable def tauLin (v : Fin 3 → F) : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
  (2 / gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v) •
    (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v).smulRight v - LinearMap.id

theorem tauLin_apply (v y : Fin 3 → F) :
    tauLin h v y = (2 * (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v y /
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v)) • v - y := by
  simp only [tauLin, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.id_apply, smul_smul]
  congr 2
  ring

variable {h}

section Tau

variable {v : Fin 3 → F} (hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0)
include hv

theorem tauLin_self : tauLin h v v = v := by
  rw [tauLin_apply, div_self hv, mul_one, two_smul, add_sub_cancel_right]

theorem gramForm_tauLin (y : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v (tauLin h v y) =
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v y := by
  rw [tauLin_apply, map_sub, map_smul, smul_eq_mul]
  field_simp
  ring

theorem tauLin_tauLin (y : Fin 3 → F) : tauLin h v (tauLin h v y) = y := by
  rw [tauLin_apply h v (tauLin h v y), gramForm_tauLin hv, tauLin_apply]
  abel

theorem tauLin_isometry (x y : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) (tauLin h v x) (tauLin h v y) =
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y := by
  have hbv := bar_gramForm h v v
  have hbx := bar_gramForm h v x
  rw [tauLin_apply, tauLin_apply]
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    map_mul, map_div₀, hbv, hbx, map_ofNat, RingHom.id_apply]
  field_simp
  ring

omit hv in
theorem tauLin_smul {c : F} (hc : c ≠ 0) : tauLin h (c • v) = tauLin h v := by
  have hbc : h.bar c ≠ 0 := (h.bar_eq_zero_iff).not.mpr hc
  refine LinearMap.ext fun y => ?_
  rw [tauLin_apply, tauLin_apply, gramForm_smul_left, gramForm_smul_left, gramForm_smul_right,
    smul_smul]
  congr 1
  field_simp

theorem tauLin_eq_self_iff (y : Fin 3 → F) : tauLin h v y = y ↔ y ∈ F ∙ v := by
  have h2 := two_ne_zero' h
  constructor
  · intro hy
    rw [tauLin_apply] at hy
    refine Submodule.mem_span_singleton.mpr ⟨gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v y /
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v, ?_⟩
    have h2y : (2 : F) • y = (2 * (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v y /
        gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v)) • v := by
      rw [two_smul]
      nth_rewrite 1 [← hy]
      abel
    have := congrArg (fun z => (2 : F)⁻¹ • z) h2y
    simp only [smul_smul, inv_mul_cancel₀ h2, one_smul] at this
    rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul] at this
    exact this.symm
  · intro hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, tauLin_self hv]

omit hv in
theorem toMatrix'_tauLin : LinearMap.toMatrix' (tauLin h v) =
    (2 / gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v) •
      vecMulVec v (fun j => h.bar (v j)) - 1 := by
  ext i j
  rw [LinearMap.toMatrix'_apply, tauLin_apply, Matrix.sub_apply, Matrix.smul_apply,
    vecMulVec_apply, Matrix.one_apply, gramForm_one_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, bar_eq_cube h]
  by_cases hij : i = j
  · subst hij
    simp
    ring
  · simp [hij]
    ring

theorem det_tauLin : LinearMap.det (tauLin h v) = 1 := by
  have h2 := two_ne_zero' h
  rw [← LinearMap.det_toMatrix', toMatrix'_tauLin]
  have hdot : (fun j => h.bar (v j)) ⬝ᵥ v = gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v := by
    rw [gramForm_one_apply]
    simp [dotProduct, bar_eq_cube h]
  have hM : (2 / gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v) •
      vecMulVec v (fun j => h.bar (v j)) - 1 = -(1 + replicateCol Unit
        (-(2 / gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v) • v) *
          replicateRow Unit (fun j => h.bar (v j))) := by
    rw [← vecMulVec_eq, neg_add, neg_smul]
    simp [vecMulVec, sub_eq_neg_add]
    ext i j
    simp [mul_assoc]
  rw [hM, det_neg, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hdot,
    Fintype.card_fin, smul_eq_mul]
  field_simp
  ring

theorem tauLin_ne_id : tauLin h v ≠ LinearMap.id := by
  intro hid
  have := h.charP
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have htr := congrArg Matrix.trace (toMatrix'_tauLin (h := h) (v := v))
  rw [hid, LinearMap.toMatrix'_id, Matrix.trace_sub, Matrix.trace_smul, trace_vecMulVec,
    Matrix.trace_one, Fintype.card_fin] at htr
  have hdot : v ⬝ᵥ (fun j => h.bar (v j)) = gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v := by
    rw [gramForm_one_apply]
    simp [dotProduct, bar_eq_cube h, mul_comm]
  rw [hdot, smul_eq_mul, div_mul_cancel₀ _ hv] at htr
  push_cast at htr
  exact two_ne_zero' h (by linear_combination -htr + 2 * h3)

theorem tauMat_mul_self :
    LinearMap.toMatrix' (tauLin h v) * LinearMap.toMatrix' (tauLin h v) = 1 := by
  rw [← LinearMap.toMatrix'_mul, show tauLin h v * tauLin h v = LinearMap.id from
    LinearMap.ext (tauLin_tauLin hv), LinearMap.toMatrix'_id]

end Tau

@[expose] noncomputable def tauGL (v : Fin 3 → F)
    (hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0) : GL (Fin 3) F :=
  ⟨LinearMap.toMatrix' (tauLin h v), LinearMap.toMatrix' (tauLin h v), tauMat_mul_self hv,
    tauMat_mul_self hv⟩

section TauGL

variable {v : Fin 3 → F} (hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0)

theorem coe_tauGL :
    ((tauGL v hv : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = LinearMap.toMatrix' (tauLin h v) :=
  rfl

theorem tauGL_mulVec (y : Fin 3 → F) :
    ((tauGL v hv : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y = tauLin h v y := by
  rw [coe_tauGL, LinearMap.toMatrix'_mulVec]

theorem tauGL_mem_statedSU (hF : Nat.card F = 9) : tauGL v hv ∈ StatedSU 3 3 F := by
  rw [statedSU_eq_gramSU hF h, mem_gramSU_iff_isometry]
  refine ⟨fun x y => ?_, ?_⟩
  · rw [tauGL_mulVec, tauGL_mulVec]
    exact tauLin_isometry hv x y
  · rw [coe_tauGL, LinearMap.det_toMatrix']
    exact det_tauLin hv

theorem orderOf_tauGL : orderOf (tauGL v hv) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ fun h1 => tauLin_ne_id hv ?_
  · rw [sq]
    exact Units.ext (tauMat_mul_self hv)
  · apply LinearMap.toMatrix'.injective
    rw [LinearMap.toMatrix'_id, ← coe_tauGL hv, h1, Units.val_one]

theorem tauGL_smul {c : F} (hc : c ≠ 0)
    (hcv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) (c • v) (c • v) ≠ 0) :
    tauGL (c • v) hcv = tauGL v hv :=
  Units.ext (by rw [coe_tauGL, coe_tauGL, tauLin_smul hc])

theorem tauGL_conj {g : GL (Fin 3) F}
    (hg : ∀ x y, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ y) = gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y)
    (hgv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) ≠ 0) :
    g * tauGL v hv * g⁻¹ = tauGL ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) hgv := by
  have hgg : ∀ y, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tauGL_mulVec, tauGL_mulVec, tauLin_apply,
    tauLin_apply, Matrix.mulVec_sub, Matrix.mulVec_smul, hgg, hg v v]
  congr 3
  rw [← hg v, hgg]

end TauGL

end CFSG.LinearGroups.UnitaryThreeOverNine
