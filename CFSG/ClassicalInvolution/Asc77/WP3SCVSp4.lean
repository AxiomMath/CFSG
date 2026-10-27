module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4
public import CFSG.ClassicalInvolution.Asc77.WP3SCVSigma
import CFSG.ClassicalInvolution.Asc77.WP3SCUBGL

public section

namespace CFSG.ClassicalInvolution.Asc77.SCV

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt_positiveLong
  mat_elt_negativeLong elt)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

section Sp4

variable {F : Type} [Field F]

theorem sp4_shape_one (k : Fin 2) (σ : F ≃+* F)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (hdet : A.det ≠ 0)
    (hu : ∀ t : F, A * Matrix.transvection (Sum.inl k) (Sum.inr k) (σ t) =
      Matrix.transvection (Sum.inl k) (Sum.inr k) t * A)
    (hl : ∀ t : F, A * Matrix.transvection (Sum.inr k) (Sum.inl k) (σ t) =
      Matrix.transvection (Sum.inr k) (Sum.inl k) t * A) :
    σ = RingEquiv.refl F ∧ (∀ b, b ≠ Sum.inl k → A (Sum.inl k) b = 0) ∧
      (∀ b, b ≠ Sum.inr k → A (Sum.inr k) b = 0) ∧ (∀ a, a ≠ Sum.inl k → A a (Sum.inl k) = 0) ∧
      (∀ a, a ≠ Sum.inr k → A a (Sum.inr k) = 0) ∧
      A (Sum.inr k) (Sum.inr k) = A (Sum.inl k) (Sum.inl k) ∧ A (Sum.inl k) (Sum.inl k) ≠ 0 := by
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  obtain ⟨hr1, hc1, hd1⟩ := rel_facts (p := Sum.inl k) (q := Sum.inr k) σ A 1 h1 (hu 1)
  obtain ⟨hr2, hc2, hd2⟩ := rel_facts (p := Sum.inr k) (q := Sum.inl k) σ A 1 h1 (hl 1)
  rw [map_one] at hd1 hd2
  have hdiag : A (Sum.inr k) (Sum.inr k) = A (Sum.inl k) (Sum.inl k) := by
    linear_combination -hd1
  have hne : A (Sum.inl k) (Sum.inl k) ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero (Sum.inl k) fun b => ?_
    by_cases hb : b = Sum.inl k
    · rw [hb]; exact h0
    · exact hr2 b hb
  refine ⟨RingEquiv.ext fun t => ?_, hr2, hr1, hc1, hc2, hdiag, hne⟩
  by_cases ht : t = 0
  · rw [ht, map_zero]
    rfl
  · have := (rel_facts (p := Sum.inl k) (q := Sum.inr k) σ A t ht (hu t)).2.2
    rw [hdiag] at this
    have h3 : A (Sum.inl k) (Sum.inl k) * (σ t - t) = 0 := by linear_combination this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hne)

theorem gsp4_scalar_of_conj_fixes [Finite F] (h2 : (2 : F) ≠ 0) (A : gsp 2 F)
    (hfix : ∀ g : StatedSp 2 F, conjSp 2 F A g = g) :
    ∃ c : F, c ≠ 0 ∧ ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  have hcomm : ∀ g : StatedSp 2 F,
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mat 2 F g =
        mat 2 F g * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro g
    have h1 : (A : GL (Fin 2 ⊕ Fin 2) F) * (g : GL (Fin 2 ⊕ Fin 2) F) *
        (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ = (g : GL (Fin 2 ⊕ Fin 2) F) := by
      rw [← coe_conjSp, hfix]
    have h2' : (A : GL (Fin 2 ⊕ Fin 2) F) * (g : GL (Fin 2 ⊕ Fin 2) F) =
        (g : GL (Fin 2 ⊕ Fin 2) F) * (A : GL (Fin 2 ⊕ Fin 2) F) := by
      calc (A : GL (Fin 2 ⊕ Fin 2) F) * (g : GL (Fin 2 ⊕ Fin 2) F)
          = ((A : GL (Fin 2 ⊕ Fin 2) F) * (g : GL (Fin 2 ⊕ Fin 2) F) *
            (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹) * (A : GL (Fin 2 ⊕ Fin 2) F) := by group
        _ = (g : GL (Fin 2 ⊕ Fin 2) F) * (A : GL (Fin 2 ⊕ Fin 2) F) := by rw [h1]
    have h3 := congrArg
      (fun u : GL (Fin 2 ⊕ Fin 2) F => (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h2'
    simpa [mat_apply] using h3
  have hdet : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 2 ⊕ Fin 2) F).isUnit).ne_zero
  have hu : ∀ (k : Fin 2) (t : F),
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inl k) (Sum.inr k) ((RingEquiv.refl F) t) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have := hcomm (elt (.positiveLong k) t)
    rwa [mat_elt_positiveLong] at this
  have hl : ∀ (k : Fin 2) (t : F),
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inr k) (Sum.inl k) ((RingEquiv.refl F) t) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have := hcomm (elt (.negativeLong k) t)
    rwa [mat_elt_negativeLong] at this
  obtain ⟨-, a, b, ha, hb, hAab⟩ := sp4_shape (RingEquiv.refl F) _ hdet hu hl
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  rw [hAab] at hμ
  have hab : a * a = b * b := sp4_sq a b μ hμ
  rcases mul_self_eq_mul_self_iff.mp hab with h | h
  · refine ⟨a, ha, ?_⟩
    rw [hAab, h]
    ext i j
    by_cases hij : i = j
    · subst hij
      rcases i with k | k <;> fin_cases k <;> simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp [Matrix.one_apply_ne hij]
  · exfalso
    have hb' : b = -a := by rw [h]; ring
    have hneg : ((-a : F)) ≠ 0 := neg_ne_zero.mpr ha
    set x₀ : StatedSp 2 F := longInv F 2 0 with hx₀
    have hAx : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        (-a) • mat 2 F x₀ := by
      rw [hAab, hx₀, mat_longInv]
      ext i j
      by_cases hij : i = j
      · subst hij
        rcases i with k | k <;> fin_cases k <;> simp [hb', mem_coords]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have hx₀c : x₀ ∈ Subgroup.center (StatedSp 2 F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply mat_injective
      have h1 := hcomm g
      rw [hAx, Matrix.smul_mul, Matrix.mul_smul] at h1
      rw [map_mul, map_mul]
      exact (smul_right_injective _ hneg h1).symm
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at hx₀c
    obtain ⟨r, hr⟩ := hx₀c
    have hr' : mat 2 F x₀ = Matrix.scalar _ (r : F) := by
      rw [mat_apply, ← hr, Matrix.GeneralLinearGroup.coe_scalar]
    have e0 := congrFun (congrFun hr' (Sum.inl 0)) (Sum.inl 0)
    have e1 := congrFun (congrFun hr' (Sum.inl 1)) (Sum.inl 1)
    rw [hx₀, mat_longInv] at e0 e1
    simp [mem_coords, Matrix.scalar_apply] at e0 e1
    apply h2
    linear_combination e1 - e0

theorem sp4_sum_two_of_ne {κ : Type*} [AddCommMonoid κ] {i j : Fin 2} (hij : i ≠ j)
    (f : Fin 2 → κ) :
    ∑ x, f x = f i + f j := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_two, add_comm]

theorem sp4_sum_four_of_ne {k k' : Fin 2} (hkk : k ≠ k') (f : Fin 2 ⊕ Fin 2 → F) :
    ∑ c, f c = (f (Sum.inl k) + f (Sum.inr k)) + (f (Sum.inl k') + f (Sum.inr k')) := by
  rw [Fintype.sum_sum_type, sp4_sum_two_of_ne hkk, sp4_sum_two_of_ne hkk]
  ring

theorem sp4_block_entries {k k' : Fin 2} (hkk : k ≠ k')
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (c μ : F) (h2 : (2 : F) ≠ 0)
    (z1 : M (Sum.inl k') (Sum.inl k) = 0) (z2 : M (Sum.inl k') (Sum.inr k) = 0)
    (z3 : M (Sum.inr k') (Sum.inl k) = 0) (z4 : M (Sum.inr k') (Sum.inr k) = 0)
    (z5 : M (Sum.inl k) (Sum.inl k') = 0) (z6 : M (Sum.inl k) (Sum.inr k') = 0)
    (z7 : M (Sum.inr k) (Sum.inl k') = 0) (z8 : M (Sum.inr k) (Sum.inr k') = 0)
    (z9 : M (Sum.inl k) (Sum.inr k) = 0) (z10 : M (Sum.inr k) (Sum.inl k) = 0)
    (hdiag : M (Sum.inr k) (Sum.inr k) = M (Sum.inl k) (Sum.inl k))
    (ha : M (Sum.inl k) (Sum.inl k) ≠ 0)
    (hsq : M * M = c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
    (hμ : Mᵀ * fromBlocks 0 1 (-1) 0 * M = μ • fromBlocks 0 1 (-1) 0) :
    M (Sum.inl k') (Sum.inr k') = 0 ∧ M (Sum.inr k') (Sum.inl k') = 0 ∧
      M (Sum.inr k') (Sum.inr k') = M (Sum.inl k') (Sum.inl k') := by
  have hkk' : k' ≠ k := Ne.symm hkk
  have e1 := congrFun (congrFun hsq (Sum.inl k')) (Sum.inr k')
  have e2 := congrFun (congrFun hsq (Sum.inr k')) (Sum.inl k')
  have e3 := congrFun (congrFun hsq (Sum.inl k')) (Sum.inl k')
  have e4 := congrFun (congrFun hsq (Sum.inr k')) (Sum.inr k')
  have e5 := congrFun (congrFun hsq (Sum.inl k)) (Sum.inl k)
  have f1 := congrFun (congrFun hμ (Sum.inl k)) (Sum.inr k)
  have f2 := congrFun (congrFun hμ (Sum.inl k')) (Sum.inr k')
  simp only [Matrix.mul_apply, sp4_sum_four_of_ne hkk] at e1 e2 e3 e4 e5
  simp only [Matrix.mul_apply, sp4_sum_four_of_ne hkk, Matrix.transpose_apply] at f1 f2
  simp [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, Matrix.smul_apply] at e1 e2 e3 e4 e5
  simp [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, hkk, hkk', Matrix.smul_apply] at f1 f2
  rw [hdiag] at f1
  have hc0 : c ≠ 0 := by
    rw [← e5]
    exact mul_ne_zero ha ha
  have hμc : μ = c := by rw [← f1, e5]
  by_cases hτ : M (Sum.inl k') (Sum.inl k') + M (Sum.inr k') (Sum.inr k') = 0
  · exfalso
    have hb : M (Sum.inr k') (Sum.inr k') = -M (Sum.inl k') (Sum.inl k') := by
      linear_combination hτ
    rw [hb] at f2
    have hcm : c + μ = 0 := by linear_combination (-1 : F) * e3 + (-1 : F) * f2
    have h2c : (2 : F) * c = 0 := by linear_combination hcm - hμc
    exact hc0 ((mul_eq_zero.mp h2c).resolve_left h2)
  · have hb12 : M (Sum.inl k') (Sum.inr k') = 0 := by
      have : M (Sum.inl k') (Sum.inr k') *
          (M (Sum.inl k') (Sum.inl k') + M (Sum.inr k') (Sum.inr k')) = 0 := by
        linear_combination e1
      exact (mul_eq_zero.mp this).resolve_right hτ
    have hb21 : M (Sum.inr k') (Sum.inl k') = 0 := by
      have : M (Sum.inr k') (Sum.inl k') *
          (M (Sum.inl k') (Sum.inl k') + M (Sum.inr k') (Sum.inr k')) = 0 := by
        linear_combination e2
      exact (mul_eq_zero.mp this).resolve_right hτ
    refine ⟨hb12, hb21, ?_⟩
    rw [hb12, hb21] at e3 f2
    have hb11 : M (Sum.inl k') (Sum.inl k') ≠ 0 := by
      intro h0
      apply hc0
      rw [← e3, h0]
      ring
    have h3 : M (Sum.inl k') (Sum.inl k') *
        (M (Sum.inr k') (Sum.inr k') - M (Sum.inl k') (Sum.inl k')) = 0 := by
      linear_combination f2 - e3 + hμc
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hb11)

theorem diag_mul_comm_of_isSupp {S : Set (Fin 2 ⊕ Fin 2)} (d : Fin 2 ⊕ Fin 2 → F)
    (hd : ∀ r ∈ S, ∀ t ∈ S, d r = d t) {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hM : IsSupp S M) : Matrix.diagonal d * M = M * Matrix.diagonal d := by
  ext r t
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : r ∈ S ∧ t ∈ S
  · rw [hd r h.1 t h.2, mul_comm]
  · rw [hM r t h]
    by_cases hrt : r = t
    · subst hrt
      rw [mul_comm]
    · simp [Matrix.one_apply_ne hrt]

theorem sp4_sigma_core [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (k : Fin 2)
    (β : MulAut (StatedProj (StatedSp 2 F))) (hβ2 : β * β = 1)
    (hfix : ∀ r ∈ (longBlock F 2 k).range, β (proj 2 F r) = proj 2 F r) :
    ∀ r ∈ (longBlock F 2 (Fin.rev k)).range, β (proj 2 F r) = proj 2 F r := by
  classical
  obtain ⟨A, σ, hβ⟩ := exists_conjAut_fieldAut_sp4 h2 β
  set α : MulAut (StatedSp 2 F) := conjSp 2 F A * fieldSp 2 F σ with hα
  have hαproj : ∀ g, proj 2 F (α g) = β (proj 2 F g) := fun g => by rw [hβ]; rfl
  have hfixα : ∀ r ∈ (longBlock F 2 k).range, α r = r := by
    have : Group.IsPerfect (longRootSp2 F 2 k) := (isClassicalSL2_longRootSp2 h2 k).isPerfect h4
    refine CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU.eq_of_central_ratio
      (longRootSp2 F 2 k) α.toMonoidHom (fun r hr => ?_)
    have h : α r * r⁻¹ ∈ spScalars 2 F := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hαproj, hfix r hr, mul_inv_cancel]
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]
    exact h
  have hu : ∀ t : F, ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      Matrix.transvection (Sum.inl k) (Sum.inr k) (σ t) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro t
    have hg := hfixα (longBlock F 2 k (sl2Upper t)) ⟨_, rfl⟩
    have := rel_of_fixed A σ _ hg
    rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
  have hl : ∀ t : F, ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      Matrix.transvection (Sum.inr k) (Sum.inl k) (σ t) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro t
    have hg := hfixα (longBlock F 2 k (sl2Lower t)) ⟨_, rfl⟩
    have := rel_of_fixed A σ _ hg
    rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  have hdet : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 2 ⊕ Fin 2) F).isUnit).ne_zero
  obtain ⟨hσ, hrow1, hrow2, hcol1, hcol2, hdiag, ha⟩ := sp4_shape_one k σ _ hdet hu hl
  subst hσ
  rw [show fieldAut 2 F (RingEquiv.refl F) = 1 from map_one _, mul_one] at hβ
  have hsq : conjAut 2 F (A * A) = 1 := by rw [map_mul, ← hβ]; exact hβ2
  have hperfK : Group.IsPerfect (StatedSp 2 F) :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.isPerfect_statedSp_of_four_le h4
  have hP : ⁅(⊤ : Subgroup (StatedSp 2 F)), ⊤⁆ = ⊤ := Group.isPerfect_def.mp hperfK
  have hall : ∀ g : StatedSp 2 F, conjSp 2 F (A * A) g = g := by
    intro g
    refine CFSG.ClassicalInvolution.Asc77.eq_of_central_ratio (conjSp 2 F (A * A)).toMonoidHom hP
      (fun p _ => ?_) g trivial
    have h : conjSp 2 F (A * A) p * p⁻¹ ∈ spScalars 2 F := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, ← conjAut_proj, hsq]
      simp
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]
    exact h
  obtain ⟨c, hc0, hAA⟩ := gsp4_scalar_of_conj_fixes h2 (A * A) hall
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := ((A : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hM
  have hsqM : M * M = c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    have := hAA
    simpa [Subgroup.coe_mul, Units.val_mul] using this
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  have hkk : k ≠ Fin.rev k := by fin_cases k <;> decide
  have hcov : ∀ j : Fin 2, j = k ∨ j = Fin.rev k := by fin_cases k <;> decide
  have hinl : ∀ i j : Fin 2, i ≠ j → (Sum.inl i : Fin 2 ⊕ Fin 2) ≠ Sum.inl j :=
    fun i j h h' => h (Sum.inl.inj h')
  have hinr : ∀ i j : Fin 2, i ≠ j → (Sum.inr i : Fin 2 ⊕ Fin 2) ≠ Sum.inr j :=
    fun i j h h' => h (Sum.inr.inj h')
  have z1 : M (Sum.inl (Fin.rev k)) (Sum.inl k) = 0 := hcol1 _ (hinl _ _ hkk.symm)
  have z2 : M (Sum.inl (Fin.rev k)) (Sum.inr k) = 0 := hcol2 _ Sum.inl_ne_inr
  have z3 : M (Sum.inr (Fin.rev k)) (Sum.inl k) = 0 := hcol1 _ Sum.inr_ne_inl
  have z4 : M (Sum.inr (Fin.rev k)) (Sum.inr k) = 0 := hcol2 _ (hinr _ _ hkk.symm)
  have z5 : M (Sum.inl k) (Sum.inl (Fin.rev k)) = 0 := hrow1 _ (hinl _ _ hkk.symm)
  have z6 : M (Sum.inl k) (Sum.inr (Fin.rev k)) = 0 := hrow1 _ Sum.inr_ne_inl
  have z7 : M (Sum.inr k) (Sum.inl (Fin.rev k)) = 0 := hrow2 _ Sum.inl_ne_inr
  have z8 : M (Sum.inr k) (Sum.inr (Fin.rev k)) = 0 := hrow2 _ (hinr _ _ hkk.symm)
  have z9 : M (Sum.inl k) (Sum.inr k) = 0 := hrow1 _ Sum.inr_ne_inl
  have z10 : M (Sum.inr k) (Sum.inl k) = 0 := hrow2 _ Sum.inl_ne_inr
  obtain ⟨hb12, hb21, hb22⟩ := sp4_block_entries hkk M c μ h2 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
    hdiag ha hsqM hμ
  have hMdiag : ∀ i j : Fin 2 ⊕ Fin 2, i ≠ j → M i j = 0 := by
    have hcover : ∀ i : Fin 2 ⊕ Fin 2, i = Sum.inl k ∨ i = Sum.inr k ∨ i = Sum.inl (Fin.rev k) ∨
        i = Sum.inr (Fin.rev k) := by
      intro i
      rcases i with j | j
      · rcases hcov j with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases hcov j with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr rfl))
    intro i j hij
    rcases hcover i with rfl | rfl | rfl | rfl <;> rcases hcover j with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hij
        | assumption
  have hMd : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hMdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  intro r hr
  obtain ⟨h, rfl⟩ := hr
  have hcomm : M * mat 2 F (longBlock F 2 (Fin.rev k) h) =
      mat 2 F (longBlock F 2 (Fin.rev k) h) * M := by
    rw [hMd]
    refine diag_mul_comm_of_isSupp (fun i => M i i) ?_ (isSupp_longBlock (Fin.rev k) h)
    intro r hr t ht
    rcases mem_coords.mp hr with rfl | rfl <;> rcases mem_coords.mp ht with rfl | rfl
    · rfl
    · exact hb22.symm
    · exact hb22
    · rfl
  have hconj : conjSp 2 F A (longBlock F 2 (Fin.rev k) h) = longBlock F 2 (Fin.rev k) h := by
    apply Subtype.ext
    rw [coe_conjSp]
    have h1 : (A : GL (Fin 2 ⊕ Fin 2) F) * ((longBlock F 2 (Fin.rev k) h : StatedSp 2 F) :
        GL (Fin 2 ⊕ Fin 2) F) = ((longBlock F 2 (Fin.rev k) h : StatedSp 2 F) :
        GL (Fin 2 ⊕ Fin 2) F) * (A : GL (Fin 2 ⊕ Fin 2) F) := by
      apply Units.ext
      simpa [Units.val_mul, mat_apply, hM] using hcomm
    calc (A : GL (Fin 2 ⊕ Fin 2) F) * ((longBlock F 2 (Fin.rev k) h : StatedSp 2 F) :
          GL (Fin 2 ⊕ Fin 2) F) * (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹
        = (((longBlock F 2 (Fin.rev k) h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
            (A : GL (Fin 2 ⊕ Fin 2) F)) * (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ := by rw [h1]
      _ = ((longBlock F 2 (Fin.rev k) h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) := by group
  rw [hβ, conjAut_proj, hconj]

theorem sp4_sigma_pair [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {R R' : Subgroup (StatedSp 2 F)} (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i)
    (hne : R ≠ R') {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F)) (β : MulAut (StatedProj (StatedSp 2 F)))
    (hβ2 : β * β = 1) (hβ : ∀ r ∈ R, β (proj 2 F r) = proj 2 F r) :
    ∀ r ∈ R', β (proj 2 F r) = proj 2 F r := by
  obtain ⟨g, k, hRg, hR'g⟩ := twin_std_sp h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  set c : MulAut (StatedProj (StatedSp 2 F)) := MulAut.conj (proj 2 F g) with hcdef
  have hcp : ∀ s, c (proj 2 F s) = proj 2 F (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set β' : MulAut (StatedProj (StatedSp 2 F)) := c⁻¹ * β * c with hβ'def
  have hβ'p : ∀ s, β' (proj 2 F s) = (c⁻¹) (β (c (proj 2 F s))) := fun s => rfl
  have hfix1 : ∀ r ∈ (longBlock F 2 k).range, β' (proj 2 F r) = proj 2 F r := by
    intro r hr
    have hmem : g * r * g⁻¹ ∈ (longBlock F 2 k).range.map (MulAut.conj g).toMonoidHom :=
      ⟨r, hr, rfl⟩
    rw [← hRg] at hmem
    rw [hβ'p, hcp, hβ _ hmem, ← hcp]
    simp
  have hβ'2 : β' * β' = 1 := by
    have : β' * β' = c⁻¹ * (β * β) * c := by rw [hβ'def]; group
    rw [this, hβ2]; group
  have hres := sp4_sigma_core h2 h4 k β' hβ'2 hfix1
  intro r hr
  rw [hR'g] at hr
  obtain ⟨b, hb, rfl⟩ := hr
  have h1 := hres b hb
  have h3 : β (c (proj 2 F b)) = c (β' (proj 2 F b)) := by
    rw [hβ'def]
    simp
  show β (proj 2 F (g * b * g⁻¹)) = proj 2 F (g * b * g⁻¹)
  rw [← hcp b, h3, h1]

end Sp4

section Model

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.FrameVertex

variable {p : ℕ} [Fact p.Prime]

theorem smallSigma_psp2 (e : ℕ) : SmallSigma p .PSp 2 e := by
  intro hp2 hq hadm H _ ψ hker R R' hR hR' hne hcomm x x' hxR hx2 hx1 hx'R' hx'2 hx'1 hc v hv2 hvR
  have hf : 1 ≤ e := hadm.2.1
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by omega)]
    omega
  have : Group.IsPerfect (modelUniv .PSp 2 p e Fact.out).K :=
    Group.isPerfect_def.2 (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSp 2 p e
      Fact.out trivial hadm).1.1
  have hxx : x' * x⁻¹ ∈ Subgroup.center (modelUniv .PSp 2 p e Fact.out).K := by
    have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [h1, ← hcomm x hxR x' hx'R']
    exact hc
  refine outer_fix_of_sq_one ψ hker (proj 2 (GaloisField p e)) proj_surjective ?_ ?_ v hv2 hvR
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · intro φ hφ2 hφR r' hr'
    exact sp4_sigma_pair h2 h4
      ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hR))
      ((exists_isLongRootSp2_iff h2 R').mpr ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'))
      hne hxR hx2 hx1 hx'R' hx'2 hx'1 hxx φ hφ2 hφR r' hr'

end Model

end CFSG.ClassicalInvolution.Asc77.SCV
