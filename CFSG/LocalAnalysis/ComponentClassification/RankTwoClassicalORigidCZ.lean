module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidIso
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidXt

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Param

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι] [DecidableEq ι]
  (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

theorem eq_of_qEGL_eq {u u' : Fin 2 → ι₂ → K} {c c' : K}
    (h : qEGL oe Q₂ u c = qEGL oe Q₂ u' c') : u = u' := by
  have h1 := congrArg (fun g : GL ι K => avec₂ oe (g : Matrix ι ι K)) h
  simpa only [coe_qEGL, avec₂_qE] using h1

theorem eq_of_qEGL_zero_eq {a a' : K} (h : qEGL oe Q₂ 0 a = qEGL oe Q₂ 0 a') : a = a' := by
  have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) (ox oe 1) (oy oe 0)) h
  simp only [coe_qEGL, qE_zero_left, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1
  have h2 : oN₀ K oe (ox oe 1) (oy oe 0) = 1 := by
    simp [oN₀]
  have h3 : (1 : Matrix ι ι K) (ox oe 1) (oy oe 0) = 0 :=
    Matrix.one_apply_ne (ox_ne_oy oe 1 0)
  rw [h2, h3, mul_one, mul_one, zero_add, zero_add] at h1
  exact h1

theorem qEGL_conj_qEGL (u u' : Fin 2 → ι₂ → K) (c : K) :
    qEGL oe Q₂ u c * qEGL oe Q₂ u' 0 * (qEGL oe Q₂ u c)⁻¹ =
      qEGL oe Q₂ u' (Q₂.polarBilin (u' 0) (u 1) + Q₂.polarBilin (u 0) (u' 1)) := by
  have h := qE_commutator oe Q₂ u u' c 0
  rw [commutatorElement_def] at h
  calc qEGL oe Q₂ u c * qEGL oe Q₂ u' 0 * (qEGL oe Q₂ u c)⁻¹ =
      (qEGL oe Q₂ u c * qEGL oe Q₂ u' 0 * (qEGL oe Q₂ u c)⁻¹ * (qEGL oe Q₂ u' 0)⁻¹) *
        qEGL oe Q₂ u' 0 := by group
    _ = qEGL oe Q₂ 0 (Q₂.polarBilin (u' 0) (u 1) + Q₂.polarBilin (u 0) (u' 1)) *
        qEGL oe Q₂ u' 0 := by rw [h]
    _ = _ := by
      apply Units.ext
      rw [Units.val_mul, coe_qEGL, coe_qEGL, coe_qEGL, qE_mul]
      congr 1
      · simp
      · simp

end Param

section Commute

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit hQ [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem exists_ne_zero_vec [Nonempty ι₂] : ∃ w : ι₂ → K, w ≠ 0 := by
  obtain ⟨a⟩ := (inferInstance : Nonempty ι₂)
  classical
  refine ⟨Pi.single a 1, fun h => ?_⟩
  have := congrFun h a
  simp at this

theorem eq_qEGL_zero_of_commute [Nonempty ι₂] (hnd : Q₂.polarBilin.Nondegenerate) {g : GL ι K}
    (hgQ : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v)
    (hg : ∀ u c, g * qEGL oe Q₂ u c = qEGL oe Q₂ u c * g) : ∃ a : K, g = qEGL oe Q₂ 0 a := by
  have hgC : g ∈ cenM₀ K oe := by
    rw [mem_centralizer_singleton_iff, ← qEGL_zero oe Q₂]
    exact hg 0 1
  obtain ⟨A, u, c, hA, hdec⟩ := eq_levi_mul_qE hQ hgC hgQ
  set Y : GL ι₂ K := (uBlkHom K oe).toHomUnits ⟨g, hgC⟩ with hYdef
  have hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w :=
    isometry_uBlk hQ (commute_oN₀_of_mem hgC) hgQ
  set l := oKappaGL oe Y * oRhoTwoGL oe A with hl
  have hact : ∀ u' : Fin 2 → ι₂ → K, ∀ t,
      u' t = (Y : Matrix ι₂ ι₂ K) *ᵥ ∑ r, (A : Matrix (Fin 2) (Fin 2) K) t r • u' r := by
    intro u' t
    obtain ⟨c', hc'⟩ := conj_qE_levi hQ hY A u'
      (Q₂.polarBilin (u' 0) (u 1) + Q₂.polarBilin (u 0) (u' 1))
    have h1 : g * qEGL oe Q₂ u' 0 * g⁻¹ = qEGL oe Q₂ u' 0 := by
      rw [hg u' 0, mul_inv_cancel_right]
    rw [hdec, show l * qEGL oe Q₂ u c * qEGL oe Q₂ u' 0 * (l * qEGL oe Q₂ u c)⁻¹ =
      l * (qEGL oe Q₂ u c * qEGL oe Q₂ u' 0 * (qEGL oe Q₂ u c)⁻¹) * l⁻¹ by group,
      qEGL_conj_qEGL, hc'] at h1
    exact congrFun (eq_of_qEGL_eq oe Q₂ h1) t |>.symm
  obtain ⟨w, hw⟩ := exists_ne_zero_vec (K := K) (ι₂ := ι₂)
  have hYw : ∀ v : ι₂ → K, (Y : Matrix ι₂ ι₂ K) *ᵥ v = 0 → v = 0 := fun v hv => by
    have := congrArg (fun x => ((Y⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ x) hv
    simpa [mulVec_mulVec] using this
  have hoff : ∀ {a : K}, (Y : Matrix ι₂ ι₂ K) *ᵥ (a • w) = 0 → a = 0 := fun {a} h => by
    rw [mulVec_smul] at h
    by_contra hne
    exact hw (hYw w ((smul_eq_zero.mp h).resolve_left hne))
  have hA10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have h := hact ![w, 0] 1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_zero, add_zero] at h
    exact hoff h.symm
  have hA01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have h := hact ![0, w] 0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_zero, zero_add] at h
    exact hoff h.symm
  have hA00 : ∀ v, v = (A : Matrix (Fin 2) (Fin 2) K) 0 0 • ((Y : Matrix ι₂ ι₂ K) *ᵥ v) :=
    fun v => by
      have h := hact ![v, 0] 0
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        smul_zero, add_zero] at h
      rwa [mulVec_smul] at h
  have hA11 : ∀ v, v = (A : Matrix (Fin 2) (Fin 2) K) 1 1 • ((Y : Matrix ι₂ ι₂ K) *ᵥ v) :=
    fun v => by
      have h := hact ![0, v] 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        smul_zero, zero_add] at h
      rwa [mulVec_smul] at h
  have heq : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = (A : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    have h := (hA00 w).symm.trans (hA11 w)
    rw [← sub_eq_zero, ← sub_smul] at h
    by_contra hne
    exact hw (hYw w ((smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)))
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := A.2
  rw [det_fin_two, hA10, hA01, ← heq, mul_zero, sub_zero] at hdet
  have h00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h1 : ((A : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * ((A : Matrix (Fin 2) (Fin 2) K) 0 0 - 1)
        = 0 := by
      linear_combination hdet + (1 - (A : Matrix (Fin 2) (Fin 2) K) 0 0) *
        CharTwo.two_eq_zero (R := K)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h1)
  have hA1 : A = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA10, hA01, h00, ← heq]
  have hY1 : Y = 1 := by
    apply Units.ext
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have h := hA00 v
    rw [h00, one_smul] at h
    rw [Units.val_one, one_mulVec]
    exact h.symm
  have hgq : g = qEGL oe Q₂ u c := by
    rw [hdec, hl, hY1, hA1, map_one, map_one, one_mul, one_mul]
  have hzero : ∀ u' : Fin 2 → ι₂ → K,
      Q₂.polarBilin (u' 0) (u 1) + Q₂.polarBilin (u 0) (u' 1) = 0 := by
    intro u'
    have h1 : g * qEGL oe Q₂ u' 0 * g⁻¹ = qEGL oe Q₂ u' 0 := by
      rw [hg u' 0, mul_inv_cancel_right]
    rw [hgq, qEGL_conj_qEGL] at h1
    have hsplit : ∀ a, qEGL oe Q₂ u' a = qEGL oe Q₂ u' 0 * qEGL oe Q₂ 0 a := fun a => by
      apply Units.ext
      rw [Units.val_mul, coe_qEGL, coe_qEGL, coe_qEGL, qE_mul]
      congr 1 <;> simp
    rw [hsplit (Q₂.polarBilin (u' 0) (u 1) + Q₂.polarBilin (u 0) (u' 1))] at h1
    exact eq_of_qEGL_zero_eq oe Q₂ (mul_left_cancel (h1.trans (hsplit 0)))
  have hsym := polarBilin_comm Q₂
  have hu1 : u 1 = 0 := hnd.1 _ fun v => by
    have h := hzero ![v, 0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_zero,
      add_zero] at h
    rw [hsym]
    exact h
  have hu0 : u 0 = 0 := hnd.1 _ fun v => by
    have h := hzero ![0, v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_zero,
      LinearMap.zero_apply, zero_add] at h
    exact h
  refine ⟨c, hgq.trans ?_⟩
  congr 1
  funext t
  fin_cases t
  · exact hu0
  · exact hu1

end Commute

end CFSG.ComponentClassification.RankTwoClassical.ORigid
