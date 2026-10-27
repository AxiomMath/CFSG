module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gCls

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Thin
open scoped Matrix

theorem vbar_conj_E8 (f₀ f b) :
    vbar 8 f₀ * E8 f b * (vbar 8 f₀)⁻¹ = E8 (f + (f₀ + sh b f₀)) b := by
  unfold E8
  rw [vbar_inv]
  calc vbar 8 f₀ * (vbar 8 f * tl b) * vbar 8 f₀
      = vbar 8 (f₀ + f) * (tl b * vbar 8 f₀ * (tl b)⁻¹) * tl b := by
        rw [vbar_add]; group
    _ = vbar 8 (f₀ + f + sh b f₀) * tl b := by
        rw [tl_conj_vbar, vbar_add (f₀ + f), vbar_add f₀]
    _ = vbar 8 (f + (f₀ + sh b f₀)) * tl b := by
        congr 2; funext i; simp only [Pi.add_apply]; ring

theorem tl_comm (b c) : tl b * tl c = tl c * tl b := by
  rw [tl_mul, tl_mul, add_comm]

theorem tl_conj_E8 (c f b) : tl c * E8 f b * (tl c)⁻¹ = E8 (sh c f) b := by
  unfold E8
  calc tl c * (vbar 8 f * tl b) * (tl c)⁻¹
      = (tl c * vbar 8 f * (tl c)⁻¹) * (tl c * tl b * (tl c)⁻¹) := by group
    _ = vbar 8 (sh c f) * tl b := by rw [tl_conj_vbar, tl_comm c b]; group

@[expose] noncomputable def lin (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : AEQ 8 :=
  mkQ 8 (ofPerm (aperm A 0))

theorem permBar_lin (A) : permBar 8 (lin A) = aperm A 0 := permBar_mkQ _

theorem ofPerm_inv' (σ : Equiv.Perm (Fin 8)) : (ofPerm σ)⁻¹ = ofPerm σ⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [ofPerm_mul, mul_inv_cancel, ofPerm_one]

theorem lin_conj_tl (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    lin A * tl v * (lin A)⁻¹ = tl (A.1 *ᵥ v) := by
  have h := comm_aperm_trans A 0 v
  have h2 : aperm A 0 * aperm 1 v * (aperm A 0)⁻¹ = aperm 1 (A.1 *ᵥ v) := by
    have : aperm A 0 * aperm 1 v * (aperm A 0)⁻¹ = aperm 1 (A.1 *ᵥ v + v) * aperm 1 v := by
      calc aperm A 0 * aperm 1 v * (aperm A 0)⁻¹
          = (aperm A 0 * aperm 1 v * (aperm A 0)⁻¹ * (aperm 1 v)⁻¹) * aperm 1 v := by group
        _ = _ := by rw [h]
    rw [this, aperm_one_mul, add_assoc, two_smul_zero, add_zero]
  unfold lin tl
  rw [← map_inv, ← map_mul, ← map_mul, ofPerm_inv', ofPerm_mul, ofPerm_mul, h2]

theorem lin_conj_E8 (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (f b) :
    lin A * E8 f b * (lin A)⁻¹ = E8 (actV (aperm A 0) f) (A.1 *ᵥ b) := by
  unfold E8
  calc lin A * (vbar 8 f * tl b) * (lin A)⁻¹
      = (lin A * vbar 8 f * (lin A)⁻¹) * (lin A * tl b * (lin A)⁻¹) := by group
    _ = _ := by rw [conj_vbar (permBar_lin A), lin_conj_tl]

theorem actV_aff (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (a c) :
    actV (aperm A 0) (aff a c) = aff (a ᵥ* (A⁻¹).1) c := by
  funext i
  show aff a c ((aperm A 0).symm i) = aff (a ᵥ* (A⁻¹).1) c i
  have h1 : (aperm A 0).symm i = (aperm A 0)⁻¹ i := rfl
  rw [h1, aperm_inv_apply]
  simp only [aapply, aff, Matrix.mulVec_zero, add_zero, bin_binIdx, Matrix.dotProduct_mulVec]

theorem aperm_zero_zero (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : aperm A 0 0 = 0 := by
  rw [aperm_apply]
  simp only [aapply, Matrix.mulVec_zero, add_zero]
  have : bin 0 = 0 := bin_zero
  rw [this, Matrix.mulVec_zero, ← this, binIdx_bin]

theorem actV_dd (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b) :
    actV (aperm A 0) (dd b) = dd (A.1 *ᵥ b) := by
  funext i
  show dd b ((aperm A 0).symm i) = dd (A.1 *ᵥ b) i
  have h0 : (aperm A 0) 0 = 0 := aperm_zero_zero A
  have h1 : (aperm A 0) (binIdx b) = binIdx (A.1 *ᵥ b) := by
    rw [aperm_apply]
    simp only [aapply, add_zero, bin_binIdx]
  have e0 : ((aperm A 0).symm i = 0) ↔ (i = 0) := by rw [Equiv.symm_apply_eq, h0]
  have e1 : ((aperm A 0).symm i = binIdx b) ↔ (i = binIdx (A.1 *ᵥ b)) := by
    rw [Equiv.symm_apply_eq, h1]
  unfold dd
  simp only [e0, e1]

theorem EvF.actV {f : Fin 8 → ZMod 2} (hf : EvF f) (σ : Equiv.Perm (Fin 8)) : EvF (actV σ f) := by
  unfold EvF at *
  exact (sum_perm_apply σ f).trans hf

theorem AffP.actV {f : Fin 8 → ZMod 2} (hf : AffP f)
    (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : AffP (actV (aperm A 0) f) := by
  obtain ⟨a, c, rfl⟩ := hf
  exact ⟨_, c, actV_aff A a c⟩

theorem affP_deriv : ∀ f₀ : Fin 8 → ZMod 2, EvF f₀ → ∀ b, AffP (f₀ + sh b f₀) := by decide +kernel
theorem affP_dd_sh : ∀ b c, AffP (sh c (dd b) + dd b) := by decide +kernel

@[expose] def NormBy (S : Subgroup (AEQ 8)) (g : AEQ 8) : Prop := ∀ x ∈ S, g * x * g⁻¹ ∈ S

theorem NormBy.mul {S : Subgroup (AEQ 8)} {g h : AEQ 8} (hg : NormBy S g) (hh : NormBy S h) :
    NormBy S (g * h) := by
  intro x hx
  have e : g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group
  rw [e]
  exact hg _ (hh x hx)

theorem aperm_split (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2) :
    aperm A b = aperm 1 b * aperm A 0 := by
  rw [aperm_mul, one_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, zero_add]

theorem mem_e29Sub_decomp {g : AEQ 8} (hg : g ∈ e29Sub) :
    ∃ (f₀ : Fin 8 → ZMod 2) (b : Fin 3 → ZMod 2) (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)),
      EvF f₀ ∧ g = vbar 8 f₀ * (tl b * lin A) := by
  obtain ⟨w, hw, rfl⟩ := hg
  obtain ⟨A, b, hAb⟩ := exists_aperm_eq (hw.2 : w.perm ∈ agl32)
  refine ⟨w.vec, b, A, hw.1.1, ?_⟩
  unfold vbar tl lin
  rw [← map_mul, ← map_mul, ofPerm_mul, ← aperm_split, hAb]
  exact congrArg (mkQ 8) (eq_ofVec_mul_ofPerm w)

theorem normBy_vbar_AE {f₀} (h : EvF f₀) : NormBy AE (vbar 8 f₀) := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := mem_AE.mp hx
  have e : vbar 8 f₀ * E8 f 0 * (vbar 8 f₀)⁻¹ = E8 (f + (f₀ + sh 0 f₀)) 0 := vbar_conj_E8 f₀ f 0
  rw [e]
  exact mem_AE.mpr ⟨_, hf.add (h.add (h.sh 0)), rfl⟩

theorem normBy_tl_AE (c) : NormBy AE (tl c) := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := mem_AE.mp hx
  rw [tl_conj_E8]
  exact mem_AE.mpr ⟨_, hf.sh c, rfl⟩

theorem normBy_lin_AE (A) : NormBy AE (lin A) := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := mem_AE.mp hx
  rw [lin_conj_E8, Matrix.mulVec_zero]
  exact mem_AE.mpr ⟨_, hf.actV _, rfl⟩

theorem normBy_vbar_AT {f₀} (h : EvF f₀) : NormBy AT (vbar 8 f₀) := by
  intro x hx
  obtain ⟨f, b, hf, rfl⟩ := mem_AT.mp hx
  rw [vbar_conj_E8]
  exact mem_AT.mpr ⟨_, b, hf.add (affP_deriv f₀ h b), rfl⟩

theorem normBy_tl_AT (c) : NormBy AT (tl c) := by
  intro x hx
  obtain ⟨f, b, hf, rfl⟩ := mem_AT.mp hx
  rw [tl_conj_E8]
  exact mem_AT.mpr ⟨_, b, hf.sh c, rfl⟩

theorem normBy_lin_AT (A) : NormBy AT (lin A) := by
  intro x hx
  obtain ⟨f, b, hf, rfl⟩ := mem_AT.mp hx
  rw [lin_conj_E8]
  exact mem_AT.mpr ⟨_, _, hf.actV A, rfl⟩

theorem normBy_vbar_AD {f₀} (h : EvF f₀) : NormBy AD (vbar 8 f₀) := by
  intro x hx
  obtain ⟨f, b, hf, rfl⟩ := mem_AD.mp hx
  rw [vbar_conj_E8]
  refine mem_AD.mpr ⟨_, b, ?_, rfl⟩
  have e : (f + (f₀ + sh b f₀)) + dd b = (f + dd b) + (f₀ + sh b f₀) := by
    funext i; simp only [Pi.add_apply]; ring
  rw [e]
  exact hf.add (affP_deriv f₀ h b)

theorem normBy_tl_AD (c) : NormBy AD (tl c) := by
  intro x hx
  obtain ⟨f, b, hf, rfl⟩ := mem_AD.mp hx
  rw [tl_conj_E8]
  refine mem_AD.mpr ⟨_, b, ?_, rfl⟩
  have e : sh c f + dd b = sh c (f + dd b) + (sh c (dd b) + dd b) := by
    funext i
    simp only [Pi.add_apply, sh_apply]
    generalize f (binIdx (bin i + c)) = x
    generalize dd b (binIdx (bin i + c)) = y
    generalize dd b i = z
    revert x y z
    decide
  rw [e]
  exact (hf.sh c).add (affP_dd_sh b c)

theorem normBy_lin_AD (A) : NormBy AD (lin A) := by
  intro x hx
  obtain ⟨f, b, hf, rfl⟩ := mem_AD.mp hx
  rw [lin_conj_E8]
  refine mem_AD.mpr ⟨_, _, ?_, rfl⟩
  have e : actV (aperm A 0) f + dd (A.1 *ᵥ b) = actV (aperm A 0) (f + dd b) := by
    rw [actV_add, actV_dd]
  rw [e]
  exact hf.actV A

theorem normal_AE {g : AEQ 8} (hg : g ∈ e29Sub) : NormBy AE g := by
  obtain ⟨f₀, b, A, hf, rfl⟩ := mem_e29Sub_decomp hg
  exact (normBy_vbar_AE hf).mul ((normBy_tl_AE b).mul (normBy_lin_AE A))

theorem normal_AT {g : AEQ 8} (hg : g ∈ e29Sub) : NormBy AT g := by
  obtain ⟨f₀, b, A, hf, rfl⟩ := mem_e29Sub_decomp hg
  exact (normBy_vbar_AT hf).mul ((normBy_tl_AT b).mul (normBy_lin_AT A))

theorem normal_AD {g : AEQ 8} (hg : g ∈ e29Sub) : NormBy AD g := by
  obtain ⟨f₀, b, A, hf, rfl⟩ := mem_e29Sub_decomp hg
  exact (normBy_vbar_AD hf).mul ((normBy_tl_AD b).mul (normBy_lin_AD A))

theorem classify_normal {A : Subgroup (AEQ 8)} (hA : A ≤ e29Sub) (hsq : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card A = 64) (hz : ∀ δ ∈ affinePlanes, ∀ h : δ.card = 4, zBar δ h ∈ A) :
    ∀ g ∈ e29Sub, ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
  intro g hg a ha
  rcases classify hA hsq hcard hz with rfl | rfl | rfl
  · exact normal_AE hg a ha
  · exact normal_AT hg a ha
  · exact normal_AD hg a ha

theorem ncard_E64_le_three :
    Set.ncard {A : Subgroup (AEQ 8) | A ≤ e29Sub ∧ (∀ a ∈ A, a * a = 1) ∧ Nat.card A = 64 ∧
      ∀ δ ∈ affinePlanes, ∀ h : δ.card = 4, zBar δ h ∈ A} ≤ 3 := by
  have hsub : {A : Subgroup (AEQ 8) | A ≤ e29Sub ∧ (∀ a ∈ A, a * a = 1) ∧ Nat.card A = 64 ∧
      ∀ δ ∈ affinePlanes, ∀ h : δ.card = 4, zBar δ h ∈ A} ⊆ {AE, AT, AD} := by
    rintro A ⟨hA, hsq, hcard, hz⟩
    rcases classify hA hsq hcard hz with rfl | rfl | rfl <;> simp
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le AE {AT, AD}).trans ?_
  have h2 := Set.ncard_insert_le AT {AD}
  rw [Set.ncard_singleton] at h2
  omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
