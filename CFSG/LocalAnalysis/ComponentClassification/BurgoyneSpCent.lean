module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareEigen

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.CatalogueBSymplecticB (matrixLinIso matrixLinIso_apply
  statedSpIsometryEquiv symplecticOperatorCentralizer)
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

variable (r K) in
abbrev spCent (A : gsp r K) : Subgroup (StatedSp r K) :=
  MonoidHom.eqLocus (conjSp r K A).toMonoidHom (MonoidHom.id _)

theorem mem_spCent {A : gsp r K} {g : StatedSp r K} :
    g ∈ spCent r K A ↔
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  constructor
  · intro h
    have h1 : (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹ = g :=
      congrArg Subtype.val h
    have h2 : (A : GL (Fin r ⊕ Fin r) K) * g = g * (A : GL (Fin r ⊕ Fin r) K) := by
      calc (A : GL (Fin r ⊕ Fin r) K) * g =
          (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹ *
            (A : GL (Fin r ⊕ Fin r) K) := by group
        _ = g * (A : GL (Fin r ⊕ Fin r) K) := by rw [h1]
    exact congrArg Units.val h2
  · intro h
    apply Subtype.ext
    change (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹ = g
    have h2 : (A : GL (Fin r ⊕ Fin r) K) * g = g * (A : GL (Fin r ⊕ Fin r) K) := Units.ext h
    rw [h2, mul_inv_cancel_right]

theorem pairedSympForm_eq (x y : Fin r ⊕ Fin r → K) :
    pairedSympForm K r x y = x ⬝ᵥ (formJ r K *ᵥ y) := by
  simp [pairedSympForm, Matrix.toBilin'_apply']

theorem mem_statedSp_iff_form (g : GL (Fin r ⊕ Fin r) K) :
    g ∈ StatedSp r K ↔ ∀ x y,
      pairedSympForm K r ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ x)
        ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y) = pairedSympForm K r x y := by
  rw [CatalogueBSymplecticB.mem_statedSp_iff_isometry,
    CatalogueBAlternatingIsometry.mem_isometryGroup_iff]
  rfl

theorem toLin_apply (g : GL (Fin r ⊕ Fin r) K) (x : Fin r ⊕ Fin r → K) :
    ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) x =
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ x := by
  rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]

@[expose] def spCentEquiv (A : gsp r K) :
    spCent r K A ≃* UnitaryHigher.similitudeCentralizer (pairedSympForm K r)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin r ⊕ Fin r) K)) where
  toFun g := ⟨Matrix.GeneralLinearGroup.toLin ((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K), by
    refine ⟨fun x y => ?_, ?_⟩
    · rw [toLin_apply, toLin_apply]
      exact (mem_statedSp_iff_form _).1 (g : StatedSp r K).2 x y
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← map_mul, ← map_mul]
      congr 1
      exact Units.ext (mem_spCent.1 g.2).symm⟩
  invFun h := ⟨⟨Matrix.GeneralLinearGroup.toLin.symm (h : LinearMap.GeneralLinearGroup K _),
    (mem_statedSp_iff_form _).2 fun x y => by
      have h1 := h.2.1 x y
      rw [← toLin_apply, ← toLin_apply, MulEquiv.apply_symm_apply]
      exact h1⟩, by
    rw [mem_spCent]
    have h2 := mem_centralizer_singleton_iff.1 h.2.2
    have h3 : Matrix.GeneralLinearGroup.toLin.symm (h : LinearMap.GeneralLinearGroup K _) *
        (A : GL (Fin r ⊕ Fin r) K) = (A : GL (Fin r ⊕ Fin r) K) *
          Matrix.GeneralLinearGroup.toLin.symm (h : LinearMap.GeneralLinearGroup K _) := by
      apply Matrix.GeneralLinearGroup.toLin.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h2
    exact (congrArg Units.val h3).symm⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.toLin.symm_apply_apply _
  right_inv h := by
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.toLin.apply_symm_apply _
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul _ _ _

theorem spCentEquiv_apply (A : gsp r K) (g : spCent r K A) (x : Fin r ⊕ Fin r → K) :
    (((spCentEquiv A g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K))) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) x =
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ x :=
  toLin_apply _ x

variable (r K) in
@[expose] def fixSub (A : gsp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    Subgroup (StatedSp r K) where
  carrier := {g | g ∈ spCent r K A ∧ ∀ v ∈ W,
    ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = v}
  one_mem' := ⟨one_mem _, fun v _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgW⟩ ⟨hh, hhW⟩
    refine ⟨mul_mem hg hh, fun v hv => ?_⟩
    change (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((h : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ v = v
    rw [← mulVec_mulVec, hhW v hv, hgW v hv]
  inv_mem' := by
    rintro g ⟨hg, hgW⟩
    refine ⟨inv_mem hg, fun v hv => ?_⟩
    have h1 : (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    calc (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v =
        (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
          (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) := by
          rw [hgW v hv]
      _ = v := by rw [mulVec_mulVec, h1, one_mulVec]

theorem fixSub_le (A : gsp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    fixSub r K A W ≤ spCent r K A := fun _ h => h.1

theorem conj_mem_fixSub {A : gsp r K} {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ g ∈ spCent r K A, ∀ v ∈ W,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W)
    {f : StatedSp r K} (hf : f ∈ spCent r K A) {q : StatedSp r K} (hq : q ∈ fixSub r K A W) :
    f * q * f⁻¹ ∈ fixSub r K A W := by
  refine ⟨mul_mem (mul_mem hf hq.1) (inv_mem hf), fun v hv => ?_⟩
  have hfv := hW _ (inv_mem hf) v hv
  have e : (((f * q * f⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v =
      ((f : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (((q : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
          ((((f⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v)) := by
    simp only [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec, Matrix.mul_assoc]
  rw [e, hq.2 _ hfv, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, Units.val_one, one_mulVec]

abbrev transvN (v : Fin r ⊕ Fin r → K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  vecMulVec v (v ᵥ* formJ r K)

theorem formJ_transpose : (formJ r K)ᵀ = -formJ r K := by
  rw [formJ, fromBlocks_transpose]
  simp [fromBlocks_neg]

theorem vecMul_formJ_dotProduct_self (v : Fin r ⊕ Fin r → K) :
    (v ᵥ* formJ r K) ⬝ᵥ v = 0 := by
  have h := pairedSympForm_self (k := K) (m := r) v
  rw [pairedSympForm_eq, dotProduct_mulVec] at h
  exact h

theorem transvN_conds (v : Fin r ⊕ Fin r → K) :
    (transvN v)ᵀ * formJ r K + formJ r K * transvN v = 0 ∧
      (transvN v)ᵀ * formJ r K * transvN v = 0 ∧ transvN v * transvN v = 0 := by
  set w := v ᵥ* formJ r K with hw
  have hJv : formJ r K *ᵥ v = -w := by
    rw [hw, ← mulVec_transpose, formJ_transpose, neg_mulVec, neg_neg]
  have hwv : w ⬝ᵥ v = 0 := vecMul_formJ_dotProduct_self v
  have e1 : (transvN v)ᵀ * formJ r K = vecMulVec w w := by
    rw [transpose_vecMulVec, vecMulVec_mul]
  have e2 : formJ r K * transvN v = -vecMulVec w w := by
    rw [mul_vecMulVec, hJv]
    ext i j
    simp [vecMulVec_apply, hw]
  refine ⟨by rw [e1, e2, add_neg_cancel], ?_, ?_⟩
  · rw [e1, vecMulVec_mul_vecMulVec, hwv, zero_smul, vecMulVec_zero]
  · rw [vecMulVec_mul_vecMulVec, hwv, zero_smul, vecMulVec_zero]

@[expose] def transvSp (v : Fin r ⊕ Fin r → K) (c : K) : StatedSp r K :=
  unipSp (transvN_conds v).1 (transvN_conds v).2.1 (transvN_conds v).2.2 c

theorem coe_transvSp (v : Fin r ⊕ Fin r → K) (c : K) :
    (((transvSp v c : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + c • transvN v :=
  rfl

theorem transvN_mulVec (v x : Fin r ⊕ Fin r → K) :
    transvN v *ᵥ x = pairedSympForm K r v x • v := by
  rw [pairedSympForm_eq, dotProduct_mulVec]
  ext i
  simp only [transvN, mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

section Eigen

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem exists_eigen_of_commute_vecMulVec' {D : Matrix ι ι K} {v w : ι → K} {b : ι}
    (hb : w b ≠ 0) (h : D * vecMulVec v w = vecMulVec v w * D) :
    ∃ μ : K, D *ᵥ v = μ • v := by
  rw [mul_vecMulVec, vecMulVec_mul] at h
  refine ⟨(w ᵥ* D) b / w b, ?_⟩
  ext a
  have := congrFun (congrFun h a) b
  simp only [vecMulVec_apply] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination this

omit [Fintype ι] [DecidableEq ι] in
theorem eq_smul_of_add_eq_zero {v v₀ : ι → K} {s t : K} (hs : s ≠ 0)
    (hst : s • v + t • v₀ = 0) : v = (-t / s) • v₀ := by
  have h1 : s • v = -(t • v₀) := eq_neg_of_add_eq_zero_left hst
  calc v = s⁻¹ • (s • v) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    _ = (-t / s) • v₀ := by
        rw [h1, smul_neg, smul_smul, ← neg_smul]
        congr 1
        ring

omit [DecidableEq ι] in
theorem exists_smul_of_eigen {D : Matrix ι ι K} {W : Submodule K (ι → K)}
    (h : ∀ v ∈ W, ∃ μ : K, D *ᵥ v = μ • v) : ∃ a : K, ∀ v ∈ W, D *ᵥ v = a • v := by
  by_cases hW : ∃ v₀ ∈ W, v₀ ≠ 0
  · obtain ⟨v₀, hv₀, hne⟩ := hW
    obtain ⟨a, ha⟩ := h v₀ hv₀
    refine ⟨a, fun v hv => ?_⟩
    obtain ⟨b, hb⟩ := h v hv
    obtain ⟨c, hc⟩ := h (v + v₀) (add_mem hv hv₀)
    by_cases hdep : ∃ t : K, v = t • v₀
    · obtain ⟨t, rfl⟩ := hdep
      rw [mulVec_smul, ha, smul_comm]
    · have e : (c - b) • v + (c - a) • v₀ = 0 := by
        have h1 := hc
        rw [mulVec_add, ha, hb] at h1
        have h' : c • v + c • v₀ = b • v + a • v₀ := by rw [← smul_add]; exact h1.symm
        calc (c - b) • v + (c - a) • v₀ = (c • v + c • v₀) - (b • v + a • v₀) := by
              simp only [sub_smul]
              abel
          _ = 0 := by rw [h', sub_self]
      by_cases hcb : c - b = 0
      · rw [hcb, zero_smul, zero_add] at e
        have hca : c - a = 0 := (smul_eq_zero.1 e).resolve_right hne
        rw [hb, show b = a by linear_combination hca - hcb]
      · exact absurd ⟨_, eq_smul_of_add_eq_zero hcb e⟩ hdep
  · push Not at hW
    exact ⟨0, fun v hv => by rw [hW v hv, mulVec_zero, smul_zero]⟩

end Eigen

end CFSG.ComponentClassification.Burgoyne.Sp
