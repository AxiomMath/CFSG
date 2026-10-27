module

public import CFSG.ClassicalInvolution.Phan.Frames.Basic
public import CFSG.ClassicalInvolution.Phan.Torus

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg Module Matrix
open scoped Pointwise

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

theorem mem_smul_iff (g : SUid σ m) (S : Submodule K (Fin m → K)) (v : Fin m → K) :
    v ∈ g • S ↔ g⁻¹ • v ∈ S := by
  refine (Submodule.mem_smul_pointwise_iff_exists (R := K) v g S).trans ?_
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa using hb
  · intro h
    exact ⟨g⁻¹ • v, h, smul_inv_smul g v⟩

theorem smul_span_singleton (g : SUid σ m) (v : Fin m → K) : g • (K ∙ v) = K ∙ (g • v) := by
  refine (Submodule.smul_span (R := K) g {v}).trans ?_
  rw [Set.smul_set_singleton]

theorem finrank_smul (g : SUid σ m) (S : Submodule K (Fin m → K)) :
    finrank K ↥(g • S) = finrank K S :=
  LinearEquiv.finrank_map_eq (DistribMulAction.toLinearEquiv K (Fin m → K) g) S

theorem nondeg_smul (g : SUid σ m) {S : Submodule K (Fin m → K)} (hS : Nondeg σ S) :
    Nondeg σ (g • S) := by
  intro s hs hs'
  rw [mem_smul_iff] at hs
  refine (smul_eq_zero_iff_eq g⁻¹).mp (hS _ hs fun t ht => ?_)
  have := hs' (g • t) (Submodule.smul_mem_pointwise_smul t g S ht)
  rw [← herm_smul_smul σ g, smul_inv_smul]
  exact this

theorem orth_smul (g : SUid σ m) {S T : Submodule K (Fin m → K)} (h : Orth σ S T) :
    Orth σ (g • S) (g • T) := by
  intro u hu v hv
  rw [mem_smul_iff] at hu hv
  rw [← herm_smul_smul σ g⁻¹]
  exact h _ hu _ hv

instance : SMul (SUid σ m) (Frame σ m) where
  smul g c :=
    { line := fun k => g • c.line k
      finrank_line := fun k => (finrank_smul g _).trans (c.finrank_line k)
      nondeg_line := fun k => nondeg_smul g (c.nondeg_line k)
      orth_line := fun k l hkl => orth_smul g (c.orth_line k l hkl) }

theorem Frame.smul_line (g : SUid σ m) (c : Frame σ m) (k : Fin m) :
    (g • c).line k = g • c.line k :=
  rfl

instance : MulAction (SUid σ m) (Frame σ m) where
  one_smul _ := Frame.ext (funext fun _ => one_smul _ _)
  mul_smul g h _ := Frame.ext (funext fun _ => mul_smul g h _)

theorem single_one_ne_zero (k : Fin m) : (Pi.single k 1 : Fin m → K) ≠ 0 := fun h =>
  (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h k)

variable (σ m) in
@[expose] def stdFrame : Frame σ m where
  line k := K ∙ (Pi.single k 1 : Fin m → K)
  finrank_line k := finrank_span_singleton (single_one_ne_zero k)
  nondeg_line k := nondeg_span_singleton (by rw [herm_single_left]; simp)
  orth_line k l hkl := orth_span_singleton_iff.2 (by
    rw [herm_single_left, Pi.single_eq_of_ne hkl, mul_zero])

theorem stdFrame_line (k : Fin m) : (stdFrame σ m).line k = K ∙ (Pi.single k 1 : Fin m → K) :=
  rfl

theorem smul_single_diagSU {m : ℕ} (d : Fin m → normOne σ) (hd : d ∈ detKer σ m) (k : Fin m) :
    diagSU σ d hd • (Pi.single k 1 : Fin m → K) =
      ((d k : normOne σ) : Kˣ).val • (Pi.single k 1 : Fin m → K) := by
  rw [diagSU_smul]
  funext a
  by_cases h : a = k
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem smul_stdFrame_eq_iff (g : SUid σ m) :
    g • stdFrame σ m = stdFrame σ m ↔ g ∈ torus σ m := by
  constructor
  · intro h
    rw [mem_torus_iff]
    intro a b hab
    have h1 : g • (K ∙ (Pi.single b 1 : Fin m → K)) = K ∙ (Pi.single b 1 : Fin m → K) :=
      congrArg (fun c : Frame σ m => c.line b) h
    have h2 : g • (Pi.single b 1 : Fin m → K) ∈ K ∙ (Pi.single b 1 : Fin m → K) :=
      h1 ▸ Submodule.smul_mem_pointwise_smul _ g _ (Submodule.mem_span_singleton_self _)
    obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h2
    have h3 := congrFun hu a
    rw [Pi.smul_apply, Pi.single_eq_of_ne hab, smul_zero, smul_def, Matrix.mulVec_single_one] at h3
    simpa [eq_comm] using h3
  · rintro ⟨⟨d, hd⟩, rfl⟩
    refine Frame.ext (funext fun k => ?_)
    change diagSUHom σ m ⟨d, hd⟩ • (K ∙ (Pi.single k 1 : Fin m → K)) =
      K ∙ (Pi.single k 1 : Fin m → K)
    rw [smul_span_singleton, diagSUHom_apply, smul_single_diagSU,
      Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (Units.ne_zero _))]

section Transitive

variable (hσ : IsUnitaryInvolution σ)
include hσ

omit hσ in
theorem norm_det_colMat {v : Fin m → Fin m → K}
    (hv : ∀ j k, herm σ (v j) (v k) = if j = k then 1 else 0) :
    σ (colMat v).det * (colMat v).det = 1 := by
  have h := congrArg Matrix.det (conjTr_colMat_mul_colMat hv)
  rw [Matrix.det_mul, Matrix.det_one, conjTr, Matrix.det_transpose] at h
  have h2 : ((colMat v).map σ).det = σ (colMat v).det :=
    (RingHom.map_det (σ : K →+* K) (colMat v)).symm
  rwa [h2] at h

omit hσ in
theorem exists_mem_SUid_smul_single {n : ℕ} {v : Fin (n + 1) → Fin (n + 1) → K}
    (hv : ∀ j k, herm σ (v j) (v k) = if j = k then 1 else 0) :
    ∃ g : SUid σ (n + 1), ∀ k, ∃ a : K, a ≠ 0 ∧
      g • (Pi.single k 1 : Fin (n + 1) → K) = a • v k := by
  set B := colMat v with hB
  set δ := B.det with hδ
  have hnorm : σ δ * δ = 1 := norm_det_colMat hv
  have hδ0 : δ ≠ 0 := fun h => by
    rw [h, mul_zero] at hnorm
    exact zero_ne_one hnorm
  set d : Fin (n + 1) → K := fun k => if k = 0 then δ⁻¹ else 1 with hd
  have hd0 : ∀ k, d k ≠ 0 := fun k => by
    by_cases hk : k = 0
    · simp [hd, hk, hδ0]
    · simp [hd, hk]
  have hdet : (B * Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    simp [hd, hδ0, ← hδ]
  have hMM : conjTr σ (B * Matrix.diagonal d) * (B * Matrix.diagonal d) = 1 := by
    rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ B) B,
      conjTr_colMat_mul_colMat hv, Matrix.one_mul, conjTr_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext k
    by_cases hk : k = 0
    · simp [hd, hk, ← mul_inv, hnorm]
    · simp [hd, hk]
  have hiso : ∀ x y, herm σ ((B * Matrix.diagonal d) *ᵥ x) ((B * Matrix.diagonal d) *ᵥ y) =
      herm σ x y := fun x y => by
    rw [herm_mulVec, hMM, Matrix.one_mulVec]
  refine ⟨mkSU σ (B * Matrix.diagonal d) hdet hiso, fun k => ⟨d k, hd0 k, ?_⟩⟩
  rw [mkSU_smul]
  funext a
  simp [Matrix.mulVec, dotProduct, Matrix.mul_diagonal, Pi.single_apply, hB, colMat_apply,
    mul_comm]

theorem exists_smul_stdFrame {n : ℕ} (c : Frame σ (n + 1)) :
    ∃ g : SUid σ (n + 1), g • stdFrame σ (n + 1) = c := by
  obtain ⟨v, hvl, hv⟩ := c.exists_gen hσ
  obtain ⟨g, hg⟩ := exists_mem_SUid_smul_single hv
  refine ⟨g, Frame.ext (funext fun k => ?_)⟩
  obtain ⟨a, ha, hga⟩ := hg k
  change g • (K ∙ (Pi.single k 1 : Fin (n + 1) → K)) = c.line k
  rw [smul_span_singleton, hga, hvl k, Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha)]

theorem exists_smul_eq {n : ℕ} (c d : Frame σ (n + 1)) : ∃ g : SUid σ (n + 1), g • c = d := by
  obtain ⟨g, rfl⟩ := exists_smul_stdFrame hσ c
  obtain ⟨h, rfl⟩ := exists_smul_stdFrame hσ d
  exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

end Transitive

end CFSG.ClassicalInvolution.Phan
