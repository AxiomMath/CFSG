module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public noncomputable section

namespace CFSG.ComponentClassification.PSL3Four

open Matrix CFSG.LocalAnalysis.ComponentInitial

@[expose] def frob : F4 ≃+* F4 where
  toFun x := x ^ 2
  invFun x := x ^ 2
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide
  map_mul' := by decide
  map_add' := by decide

theorem frob_apply (x : F4) : frob x = x ^ 2 := rfl

theorem ringEquiv_eq (σ : F4 ≃+* F4) : σ = RingEquiv.refl F4 ∨ σ = frob := by
  have hω : σ F4.ω * σ F4.ω + σ F4.ω + 1 = 0 := by
    have h := congrArg σ (show F4.ω * F4.ω + F4.ω + 1 = 0 by decide)
    rwa [map_add, map_add, map_mul, map_one, map_zero] at h
  have hall : ∀ x : F4, x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = 1 + F4.ω := by decide
  rcases (F4.roots_quadratic (σ F4.ω)).1 hω with h | h
  · left
    refine RingEquiv.ext fun x => ?_
    rcases hall x with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simpa using h
    · simp [map_add, h]
  · right
    refine RingEquiv.ext fun x => ?_
    rw [frob_apply]
    rcases hall x with rfl | rfl | rfl | rfl
    · rw [map_zero]
      decide
    · rw [map_one]
      decide
    · rw [h]
      decide
    · rw [map_add, map_one, h]
      decide

abbrev sqv (v : Vec) : Vec := fun k => v k ^ 2

theorem sqv_eq (v : Vec) : sqv v = frob.toRingHom ∘ v := rfl

theorem sq_eq_zero_iff (x : F4) : x ^ 2 = 0 ↔ x = 0 := by revert x; decide

theorem sqv_ne_zero {v : Vec} (hv : v ≠ 0) : sqv v ≠ 0 := by
  intro h
  apply hv
  funext k
  exact (sq_eq_zero_iff _).1 (congrFun h k)

theorem sqv_sqv (v : Vec) : sqv (sqv v) = v := by
  funext k
  exact (show ∀ x : F4, (x ^ 2) ^ 2 = x by decide) (v k)

theorem sqv_smul (c : F4) (v : Vec) : sqv (c • v) = c ^ 2 • sqv v := by
  funext k
  show (c * v k) ^ 2 = c ^ 2 * v k ^ 2
  exact mul_pow c (v k) 2

theorem lead_sqv (u : Vec) : lead (sqv u) = lead u ^ 2 := by
  unfold lead
  simp only [ne_eq, sq_eq_zero_iff]
  split_ifs <;> rfl

theorem normalize_sqv (u : Vec) : normalize (sqv u) = sqv (normalize u) := by
  funext k
  show (lead (sqv u))⁻¹ * u k ^ 2 = ((lead u)⁻¹ * u k) ^ 2
  rw [lead_sqv, mul_pow, inv_pow]

theorem vIdx_normalize (u : Vec) : vIdx (normalize u) = vIdx u := by
  rw [vIdx, vIdx, normalize_normalize]

theorem vIdx_sqv_normalize (u : Vec) : vIdx (sqv (normalize u)) = vIdx (sqv u) := by
  rw [← normalize_sqv, vIdx_normalize]

theorem sqv_mulVec (M : Matrix (Fin 3) (Fin 3) F4) (v : Vec) :
    sqv (M *ᵥ v) = M.map (· ^ 2) *ᵥ sqv v := by
  funext k
  exact RingHom.map_mulVec frob.toRingHom M v k

theorem vIdx_frob_core (M : Matrix (Fin 3) (Fin 3) F4)
    (hM : ∀ w : Vec, w ≠ 0 → M *ᵥ w ≠ 0) {v : Vec} (hv : v ≠ 0) :
    vIdx (sqv (V.getD (vIdx (M *ᵥ V.getD (vIdx (sqv v)) 0)) 0)) =
      vIdx (M.map (· ^ 2) *ᵥ v) := by
  have h1 := sqv_ne_zero hv
  rw [getD_vIdx h1]
  have h2 : M *ᵥ normalize (sqv v) ≠ 0 := hM _ (normalize_ne_zero h1)
  rw [getD_vIdx h2, vIdx_sqv_normalize, normalize_eq_smul, mulVec_smul, sqv_smul,
    vIdx_smul (pow_ne_zero 2 (inv_ne_zero (lead_ne_zero h1))), sqv_mulVec, sqv_sqv]

theorem mulVec_ne_zero' (A : GL (Fin 3) F4) : ∀ w : Vec, w ≠ 0 →
    (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ w ≠ 0 := fun _ hw => mulVec_ne_zero A hw

theorem transpose_mulVec_ne_zero (A : GL (Fin 3) F4) : ∀ w : Vec, w ≠ 0 →
    ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ w ≠ 0 := fun w hw => by
  rw [← coe_invTranspose]
  exact mulVec_ne_zero _ hw

theorem g5Fun_val (i : Fin 42) : (g5Fun i).val = 21 * (i.val / 21) + vIdx (sqv (vecOf i)) := rfl

theorem vecOf_def (j : Fin 42) : vecOf j = V.getD (j.val % 21) 0 := rfl

theorem rhoFun_val (A : GL (Fin 3) F4) (i : Fin 42) : (rhoFun A i).val =
    if i.val < 21 then vIdx ((A : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf i)
    else 21 + vIdx (((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ vecOf i) := by
  unfold rhoFun
  split_ifs <;> rfl

theorem rhoFun_frob {B B' : GL (Fin 3) F4}
    (hB : (B' : Matrix (Fin 3) (Fin 3) F4) = (B : Matrix (Fin 3) (Fin 3) F4).map (· ^ 2))
    (hBi : ((B'⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      ((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).map (· ^ 2)) (i : Fin 42) :
    rhoFun B' i = g5Fun (rhoFun B (g5Fun i)) := by
  apply Fin.ext
  have hj := vIdx_lt (sqv (vecOf i))
  by_cases hi : i.val < 21
  · have hi0 : i.val / 21 = 0 := Nat.div_eq_of_lt hi
    have e1 : (rhoFun B' i).val = vIdx ((B' : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf i) := by
      rw [rhoFun_val, ite_eq_left hi]
    have e2 : (g5Fun i).val = vIdx (sqv (vecOf i)) := by rw [g5Fun_val, hi0, mul_zero, zero_add]
    have hg : (g5Fun i).val < 21 := by rw [e2]; exact hj
    have e3 : (rhoFun B (g5Fun i)).val =
        vIdx ((B : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf (g5Fun i)) := by
      rw [rhoFun_val, ite_eq_left hg]
    have e4 : vecOf (g5Fun i) = V.getD (vIdx (sqv (vecOf i))) 0 := by
      rw [vecOf_def, e2, Nat.mod_eq_of_lt hj]
    have hk : (rhoFun B (g5Fun i)).val < 21 := by rw [e3]; exact vIdx_lt _
    have e5 : (g5Fun (rhoFun B (g5Fun i))).val =
        vIdx (sqv (vecOf (rhoFun B (g5Fun i)))) := by
      rw [g5Fun_val, Nat.div_eq_of_lt hk, mul_zero, zero_add]
    have e6 : vecOf (rhoFun B (g5Fun i)) =
        V.getD (vIdx ((B : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf (g5Fun i))) 0 := by
      rw [vecOf_def, e3, Nat.mod_eq_of_lt (vIdx_lt _)]
    rw [e1, e5, e6, e4, vIdx_frob_core _ (mulVec_ne_zero' B) (vecOf_ne_zero i), hB]
  · have hi1 : i.val / 21 = 1 := by omega
    have e1 : (rhoFun B' i).val =
        21 + vIdx (((B'⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ vecOf i) := by
      rw [rhoFun_val, ite_eq_right hi]
    have e2 : (g5Fun i).val = 21 + vIdx (sqv (vecOf i)) := by rw [g5Fun_val, hi1, mul_one]
    have hg : ¬ (g5Fun i).val < 21 := by rw [e2]; omega
    have e3 : (rhoFun B (g5Fun i)).val =
        21 + vIdx (((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ vecOf (g5Fun i)) := by
      rw [rhoFun_val, ite_eq_right hg]
    have e4 : vecOf (g5Fun i) = V.getD (vIdx (sqv (vecOf i))) 0 := by
      rw [vecOf_def, e2, Nat.add_mod_left, Nat.mod_eq_of_lt hj]
    have hk := vIdx_lt (((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ vecOf (g5Fun i))
    have hk1 : (rhoFun B (g5Fun i)).val / 21 = 1 := by rw [e3]; omega
    have e5 : (g5Fun (rhoFun B (g5Fun i))).val =
        21 + vIdx (sqv (vecOf (rhoFun B (g5Fun i)))) := by
      rw [g5Fun_val, hk1, mul_one]
    have e6 : vecOf (rhoFun B (g5Fun i)) = V.getD (vIdx
        (((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ vecOf (g5Fun i))) 0 := by
      rw [vecOf_def, e3, Nat.add_mod_left, Nat.mod_eq_of_lt hk]
    rw [e1, e5, e6, e4, vIdx_frob_core _ (transpose_mulVec_ne_zero B) (vecOf_ne_zero i), hBi,
      transpose_map]

theorem g6Fun_val (i : Fin 42) :
    (g6Fun i).val = if i.val < 21 then i.val + 21 else i.val - 21 := by
  unfold g6Fun
  split_ifs <;> rfl

theorem rhoFun_invTranspose (A : GL (Fin 3) F4) (i : Fin 42) :
    rhoFun (invTranspose A) i = g6Fun (rhoFun A (g6Fun i)) := by
  apply Fin.ext
  by_cases hi : i.val < 21
  · have e1 : (g6Fun i).val = i.val + 21 := by rw [g6Fun_val, ite_eq_left hi]
    have hg : ¬ (g6Fun i).val < 21 := by rw [e1]; omega
    have hv : vecOf (g6Fun i) = vecOf i := by
      rw [vecOf_def, vecOf_def, e1, Nat.add_mod_right]
    have e2 : (rhoFun A (g6Fun i)).val =
        21 + vIdx (((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)ᵀ *ᵥ vecOf i) := by
      rw [rhoFun_val, ite_eq_right hg, hv]
    have hk : ¬ (rhoFun A (g6Fun i)).val < 21 := by rw [e2]; omega
    rw [g6Fun_val, ite_eq_right hk, e2, rhoFun_val, ite_eq_left hi, coe_invTranspose]
    omega
  · have e1 : (g6Fun i).val = i.val - 21 := by rw [g6Fun_val, ite_eq_right hi]
    have hg : (g6Fun i).val < 21 := by rw [e1]; omega
    have hv : vecOf (g6Fun i) = vecOf i := by
      rw [vecOf_def, vecOf_def, e1]
      congr 1
      omega
    have e2 : (rhoFun A (g6Fun i)).val = vIdx ((A : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf i) := by
      rw [rhoFun_val, ite_eq_left hg, hv]
    have hk : (rhoFun A (g6Fun i)).val < 21 := by rw [e2]; exact vIdx_lt _
    have hinv : (((invTranspose A)⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        (A : Matrix (Fin 3) (Fin 3) F4)ᵀ := rfl
    rw [g6Fun_val, ite_eq_left hk, e2, rhoFun_val, ite_eq_right hi, hinv, transpose_transpose]
    omega

theorem g₅_mul_g₅ : g₅ * g₅ = 1 := Equiv.ext g5Fun_g5Fun

theorem g₆_mul_g₆ : g₆ * g₆ = 1 := Equiv.ext g6Fun_g6Fun

theorem rho_frob {B B' : GL (Fin 3) F4}
    (hB : (B' : Matrix (Fin 3) (Fin 3) F4) = (B : Matrix (Fin 3) (Fin 3) F4).map (· ^ 2))
    (hBi : ((B'⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      ((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).map (· ^ 2)) :
    rho B' = g₅ * rho B * g₅⁻¹ := by
  rw [inv_eq_of_mul_eq_one_left g₅_mul_g₅]
  exact Equiv.ext fun i => rhoFun_frob hB hBi i

theorem rho_invTranspose (A : GL (Fin 3) F4) : rho (invTranspose A) = g₆ * rho A * g₆⁻¹ := by
  rw [inv_eq_of_mul_eq_one_left g₆_mul_g₆]
  exact Equiv.ext fun i => rhoFun_invTranspose A i

theorem rho_mem_S_of_det {B : GL (Fin 3) F4} (hB : (B : Matrix (Fin 3) (Fin 3) F4).det = 1) :
    rho B ∈ S := by
  rw [← range_rhoSL.1]
  have e : SpecialLinearGroup.toGL (⟨B, hB⟩ : SpecialLinearGroup (Fin 3) F4) = B := Units.ext rfl
  exact ⟨(⟨B, hB⟩ : SpecialLinearGroup (Fin 3) F4), congrArg rho e⟩

theorem det_dGL_inv :
    (((dGL⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)).det = 1 + F4.ω := by
  show (diagonal ![1 + F4.ω, 1, 1]).det = 1 + F4.ω
  rw [det_fin_three]
  decide

theorem rho_mem_R (A : GL (Fin 3) F4) : rho A ∈ R := by
  have hdet : (A : Matrix (Fin 3) (Fin 3) F4).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A) |>.ne_zero
  have hcases : ∀ x : F4, x ≠ 0 → x = 1 ∨ x = F4.ω ∨ x = F4.ω * F4.ω := by decide
  have hg4 : rho dGL ∈ R := g₄_mem_R
  rcases hcases _ hdet with h | h | h
  · exact S_le_R (rho_mem_S_of_det h)
  · have hB : ((A * dGL⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
      rw [Units.val_mul, det_mul, h, det_dGL_inv]
      decide
    have := Subgroup.mul_mem _ (S_le_R (rho_mem_S_of_det hB)) hg4
    rwa [← map_mul, inv_mul_cancel_right] at this
  · have hB : ((A * dGL⁻¹ * dGL⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, h, det_dGL_inv]
      decide
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (S_le_R (rho_mem_S_of_det hB)) hg4) hg4
    rwa [← map_mul, ← map_mul, inv_mul_cancel_right, inv_mul_cancel_right] at this

@[expose] def conjAutS : R →* MulAut S where
  toFun r :=
    { toFun := fun s => ⟨r * s * r⁻¹, conj_mem_S r.2 s.2⟩
      invFun := fun s => ⟨r⁻¹ * s * r, by
        have := conj_mem_S (R.inv_mem r.2) s.2
        rwa [inv_inv] at this⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext s
    simp
  map_mul' r r' := by
    ext s
    simp [mul_assoc]

theorem conjAutS_apply (r : R) (s : S) :
    ((conjAutS r s : S) : Equiv.Perm (Fin 42)) =
      (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ := rfl

theorem conjAutS_injective : Function.Injective conjAutS := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro r hr
  rw [MonoidHom.mem_ker] at hr
  have hc : (r : Equiv.Perm (Fin 42)) ∈ Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := congrArg (fun α : MulAut S => ((α ⟨s, hs⟩ : S) : Equiv.Perm (Fin 42))) hr
    simp only [conjAutS_apply, MulAut.one_apply] at h
    calc s * (r : Equiv.Perm (Fin 42))
        = (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ * r := by rw [h]
      _ = r * s := by group
  have h1 : (r : Equiv.Perm (Fin 42)) ∈
      Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := ⟨hc, r.2⟩
  rw [centralizer_S_inf_R, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (Subtype.ext h1)

@[expose] def Realized (γ : MulAut (LinearFlag.projectiveSL 3 F4)) : Prop :=
  ∃ r ∈ R, ∀ x, (theta (γ x) : Equiv.Perm (Fin 42)) = r * theta x * r⁻¹

theorem Realized.one : Realized 1 := ⟨1, R.one_mem, fun x => by simp⟩

theorem Realized.mul {γ δ : MulAut (LinearFlag.projectiveSL 3 F4)} (hγ : Realized γ)
    (hδ : Realized δ) : Realized (γ * δ) := by
  obtain ⟨r, hr, hγr⟩ := hγ
  obtain ⟨s, hs, hδs⟩ := hδ
  refine ⟨r * s, R.mul_mem hr hs, fun x => ?_⟩
  rw [MulAut.mul_apply, hγr, hδs]
  group

theorem Realized.pow {γ : MulAut (LinearFlag.projectiveSL 3 F4)} (hγ : Realized γ) :
    ∀ k : ℕ, Realized (γ ^ k)
  | 0 => by rw [pow_zero]; exact Realized.one
  | k + 1 => by rw [pow_succ]; exact (hγ.pow k).mul hγ

theorem realized_conjAut (A : GL (Fin 3) F4) : Realized (LinearFlag.conjAut 3 F4 A) := by
  refine ⟨rho A, rho_mem_R A, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F4 x
  rw [LinearFlag.conjAut_proj, theta_proj, theta_proj,
    CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]

theorem realized_frob : Realized (LinearFlag.fieldAut 3 F4 frob) := by
  refine ⟨g₅, g₅_mem_R, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F4 x
  rw [LinearFlag.fieldAut_proj, theta_proj, theta_proj]
  apply rho_frob
  · rfl
  · rw [← map_inv, ← map_inv, ← map_inv]
    rfl

theorem realized_fieldAut (σ : F4 ≃+* F4) : Realized (LinearFlag.fieldAut 3 F4 σ) := by
  rcases ringEquiv_eq σ with rfl | rfl
  · have : LinearFlag.fieldAut 3 F4 (RingEquiv.refl F4) = 1 := map_one (LinearFlag.fieldAut 3 F4)
    rw [this]
    exact Realized.one
  · exact realized_frob

theorem realized_dualAut : Realized (LinearFlag.dualAut 3 F4) := by
  refine ⟨g₆, g₆_mem_R, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F4 x
  rw [LinearFlag.dualAut_proj, theta_proj, theta_proj, ← rho_invTranspose]
  congr 1
  apply Units.ext
  rw [coe_invTranspose, ← map_inv]
  rfl

theorem conjAutS_surjective : Function.Surjective conjAutS := by
  intro α
  let β : MulAut (LinearFlag.projectiveSL 3 F4) := (theta.trans α).trans theta.symm
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := F4) (n := 3) (by norm_num)
  obtain ⟨A, σ, ε, -, hβ⟩ := hgen β
  have hreal : Realized β := by
    rw [hβ]
    exact ((realized_conjAut A).mul (realized_fieldAut σ)).mul (realized_dualAut.pow ε)
  obtain ⟨r, hr, hβr⟩ := hreal
  refine ⟨⟨r, hr⟩, MulEquiv.ext fun s => Subtype.ext ?_⟩
  have h := hβr (theta.symm s)
  have hβs : theta (β (theta.symm s)) = α s := by simp [β]
  rw [hβs, MulEquiv.apply_symm_apply] at h
  rw [conjAutS_apply, ← h]

theorem full_automorphism_action :
    ∃ e : R ≃* MulAut S, (∀ (r : R) (s : S), ((e r s : S) : Equiv.Perm (Fin 42)) = r * s * r⁻¹) ∧
      (S.subgroupOf R).map e.toMonoidHom = (MulAut.conj : S →* MulAut S).range := by
  refine ⟨MulEquiv.ofBijective conjAutS ⟨conjAutS_injective, conjAutS_surjective⟩,
    fun r s => rfl, ?_⟩
  ext α
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, MulEquiv.ext fun s => Subtype.ext rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, S_le_R s.2⟩, s.2, MulEquiv.ext fun t => Subtype.ext rfl⟩

end CFSG.ComponentClassification.PSL3Four
