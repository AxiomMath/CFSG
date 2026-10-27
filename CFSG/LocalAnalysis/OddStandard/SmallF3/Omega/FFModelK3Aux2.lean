module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimOrth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenInr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap TauCeti

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
  {R : QuadraticForm (ZMod 3) W}

@[expose] noncomputable def frameNorm (R : QuadraticForm (ZMod 3) W) : (ZMod 3)ˣ :=
  if (-(quadSign R)) = 1 then 1 else -1

theorem toSign_frameNorm (R : QuadraticForm (ZMod 3) W) : toSign (frameNorm R) = -(quadSign R) := by
  rcases Int.units_eq_one_or (-(quadSign R)) with h | h <;>
    simp [frameNorm, h, toSign] <;> decide

theorem frameNorm_ne_zero (R : QuadraticForm (ZMod 3) W) : (frameNorm R : ZMod 3) ≠ 0 :=
  (frameNorm R).ne_zero

private theorem presentForm_apply' (u : (ZMod 3)ˣ) (x : Fin 3 → ZMod 3) :
    presentedForm (⟨3, fun _ => u⟩ : RegularFormPresentation (ZMod 3)) x =
      (u : ZMod 3) * (x 0 * x 0 + x 1 * x 1 + x 2 * x 2) := by
  rw [presentedForm_apply, Fin.sum_univ_three]
  ring

private theorem presentForm_single (u : (ZMod 3)ˣ) (i : Fin 3) :
    presentedForm (⟨3, fun _ => u⟩ : RegularFormPresentation (ZMod 3)) (Pi.single i 1) =
      (u : ZMod 3) := by
  rw [presentedForm_apply, Fin.sum_univ_three]
  fin_cases i <;> simp

private theorem presentForm_polar (u : (ZMod 3)ˣ) (x y : Fin 3 → ZMod 3) :
    polar (presentedForm (⟨3, fun _ => u⟩ : RegularFormPresentation (ZMod 3))) x y =
      2 * (u : ZMod 3) * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) := by
  rw [QuadraticMap.polar, presentForm_apply', presentForm_apply', presentForm_apply']
  simp only [Pi.add_apply]
  ring

theorem k3_frame (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) W = 3) :
    ∃ z u v : W, R z = R u ∧ R u = R v ∧ R u = (frameNorm R : ZMod 3) ∧
      polar R z u = 0 ∧ polar R z v = 0 ∧ polar R u v = 0 := by
  classical
  let u : (ZMod 3)ˣ := frameNorm R
  have hu : toSign u = -(quadSign R) := toSign_frameNorm R
  let p : RegularFormPresentation (ZMod 3) := ⟨3, fun _ => u⟩
  let Qp : QuadraticForm (ZMod 3) (Fin 3 → ZMod 3) := presentedForm p
  have hQp : Qp.Nondegenerate := nondegenerate_presentedForm p
  have hsign : quadSign Qp = quadSign R := by
    rw [quadSign_eq_signOf Qp hQp]
    rw [show formClass Qp hQp = Quotient.mk (regularFormSetoid (ZMod 3)) p from
      formClass_presentedForm p]
    rw [signOf_mk_diag]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hu]
    have h3 : (-1 : ℤˣ) ^ (3 / 2) = -1 := by decide
    rw [h3]
    rcases Int.units_eq_one_or (quadSign R) with h | h <;> rw [h] <;> decide
  have hdim' : Module.finrank (ZMod 3) (Fin 3 → ZMod 3) = Module.finrank (ZMod 3) W := by
    rw [Module.finrank_fin_fun, hdim]
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hQp hR hdim' hsign
  let b : Fin 3 → (Fin 3 → ZMod 3) := fun i => Pi.single i 1
  have hbval : ∀ i : Fin 3, Qp (b i) = (u : ZMod 3) := fun i => presentForm_single u i
  have hbne : (u : ZMod 3) ≠ 0 := u.ne_zero
  have hbpol : ∀ i j : Fin 3, i ≠ j → polar Qp (b i) (b j) = 0 := by
    intro i j hij
    rw [show Qp = presentedForm p from rfl, presentForm_polar]
    fin_cases i <;> fin_cases j <;> simp_all [b]
  refine ⟨e (b 0), e (b 1), e (b 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [e.map_app, hbval]
  · simp only [e.map_app, hbval]
  · rw [e.map_app, hbval]
  · rw [e.polar_apply]
    exact hbpol 0 1 (by decide)
  · rw [e.polar_apply]
    exact hbpol 0 2 (by decide)
  · rw [e.polar_apply]
    exact hbpol 1 2 (by decide)

theorem mul_comm_reflOf_of_orth (u v : W) (hu : R u ≠ 0) (hv : R v ≠ 0)
    (huv : polar R u v = 0) :
    reflOf R u hu * reflOf R v hv = reflOf R v hv * reflOf R u hu := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coe_reflOf_apply]
  have h1 : polar R u (x - (polar R v x / R v) • v) = polar R u x := by
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, huv, smul_zero, sub_zero]
  have h2 : polar R v (x - (polar R u x / R u) • u) = polar R v x := by
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right,
      (QuadraticMap.polar_comm R u v).symm, huv, smul_zero, sub_zero]
  rw [h1, h2]
  abel

theorem commSp_reflOf_mul_reflOf_of_orth (hR : R.Nondegenerate) (u v : W) (hu : R u ≠ 0)
    (hv : R v ≠ 0) (huv : polar R u v = 0) :
    commSp (reflOf R u hu * reflOf R v hv) =
      Submodule.span (ZMod 3) ({u, v} : Set W) := by
  set g : OGroup R := reflOf R u hu * reflOf R v hv with hg
  have hcomm := mul_comm_reflOf_of_orth u v hu hv huv
  have hgg : g * g = 1 := by
    rw [hg]
    calc (reflOf R u hu * reflOf R v hv) * (reflOf R u hu * reflOf R v hv)
        = reflOf R u hu * (reflOf R v hv * reflOf R u hu) * reflOf R v hv := by group
      _ = reflOf R u hu * (reflOf R u hu * reflOf R v hv) * reflOf R v hv := by rw [← hcomm]
      _ = 1 := by rw [← mul_assoc, reflOf_mul_self, one_mul, reflOf_mul_self]
  have hu_self : (reflOf R u hu : W ≃ₗ[ZMod 3] W) u = -u := by
    letI : Invertible (R u) := invertibleOfNonzero hu
    rw [reflOf_eq u hu, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
    exact TauCeti.QuadraticMap.reflection_apply_self R u
  have hu_g : (g : W ≃ₗ[ZMod 3] W) u = -u := by
    rw [hg, Subgroup.coe_mul, LinearEquiv.mul_apply]
    have hv' : (reflOf R v hv : W ≃ₗ[ZMod 3] W) u = u := by
      rw [coe_reflOf_apply v hv u, QuadraticMap.polar_comm R v u, huv, zero_div, zero_smul,
        sub_zero]
    rw [hv', hu_self]
  have hv_g : (g : W ≃ₗ[ZMod 3] W) v = -v := by
    rw [hg, Subgroup.coe_mul, LinearEquiv.mul_apply]
    have hv_self : (reflOf R v hv : W ≃ₗ[ZMod 3] W) v = -v := by
      letI : Invertible (R v) := invertibleOfNonzero hv
      rw [reflOf_eq v hv, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
      exact TauCeti.QuadraticMap.reflection_apply_self R v
    rw [hv_self]
    have hu' : (reflOf R u hu : W ≃ₗ[ZMod 3] W) (-v) = -v := by
      rw [map_neg, coe_reflOf_apply u hu v, huv, zero_div, zero_smul, sub_zero]
    rw [hu']
  have hspan : (Submodule.span (ZMod 3) ({(u : W), v} : Set W)) ≤ commSp g := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact (mem_commSp_iff hgg).mpr hu_g
    · exact (mem_commSp_iff hgg).mpr hv_g
  have horth_le : LinearMap.BilinForm.orthogonal R.polarBilin
      (Submodule.span (ZMod 3) ({(u : W), v} : Set W)) ≤ fixSp g := by
    intro y hy
    obtain ⟨huy, hvy⟩ := ff_mem_orth_pair_iff.mp hy
    rw [mem_fixSp_iff]
    show (g : W ≃ₗ[ZMod 3] W) y = y
    rw [hg, Subgroup.coe_mul, LinearEquiv.mul_apply, coe_reflOf_apply v hv y, hvy, zero_div,
      zero_smul, sub_zero, coe_reflOf_apply u hu y, huy, zero_div, zero_smul, sub_zero]
  have horth_fin := ff_finrank_orth_pair (Q := R) hR hu hv huv
  have hfix_fin : Module.finrank (ZMod 3) W - 2 ≤ Module.finrank (ZMod 3) (fixSp g) := by
    have h := Submodule.finrank_mono horth_le
    omega
  have hsum := finrank_fixSp_add_finrank_commSp (Q := R) g
  have hspan_fin := ff_finrank_span_pair (Q := R) hu hv huv
  have hcomm_fin : Module.finrank (ZMod 3) (commSp g) = 2 := by
    have hlow : 2 ≤ Module.finrank (ZMod 3) (commSp g) := by
      have h := Submodule.finrank_mono hspan
      rwa [hspan_fin] at h
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hspan (by rw [hspan_fin, hcomm_fin])).symm

section SigCube

variable (z u v : W)

private theorem polar_add_self' (x : W) : polar R x x = 2 * R x := by
  rw [QuadraticMap.polar_self, nsmul_eq_mul]
  norm_num

private theorem frame_linearIndependent (hzu : polar R z u = 0) (hzv : polar R z v = 0)
    (huv : polar R u v = 0) (hz : R z = R u) (huv' : R u = R v) (hne : R u ≠ 0) :
    LinearIndependent (ZMod 3) ![z, u, v] := by
  have hv : R v ≠ 0 := huv' ▸ hne
  refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := R.polarBilin) ?_ ?_
  · rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm R]
  · intro i
    fin_cases i
    · change R.polarBilin z z ≠ 0
      rw [QuadraticMap.polarBilin_apply_apply, polar_add_self']
      exact fun h => hne (by
        rw [hz] at h
        exact (mul_eq_zero.mp h).resolve_left (by decide))
    · change R.polarBilin u u ≠ 0
      rw [QuadraticMap.polarBilin_apply_apply, polar_add_self']
      exact fun h => hne ((mul_eq_zero.mp h).resolve_left (by decide))
    · change R.polarBilin v v ≠ 0
      rw [QuadraticMap.polarBilin_apply_apply, polar_add_self']
      exact fun h => hv ((mul_eq_zero.mp h).resolve_left (by decide))

theorem k3_ext (hdim : Module.finrank (ZMod 3) W = 3)
    (hzu : polar R z u = 0) (hzv : polar R z v = 0) (huv : polar R u v = 0)
    (hz : R z = R u) (huv' : R u = R v) (hne : R u ≠ 0)
    {f g : W ≃ₗ[ZMod 3] W} (hfz : f z = g z) (hfu : f u = g u) (hfv : f v = g v) : f = g := by
  have hli := frame_linearIndependent z u v hzu hzv huv hz huv' hne
  have hcard : Fintype.card (Fin 3) = Module.finrank (ZMod 3) W := by
    rw [Fintype.card_fin, hdim]
  let b : Module.Basis (Fin 3) (ZMod 3) W :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : (b : Fin 3 → W) = ![z, u, v] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  apply b.ext'
  intro i
  rw [hb]
  fin_cases i <;> assumption

@[expose] noncomputable def k3Sig (hau : R (u + z) ≠ 0) (hbv : R (v + z) ≠ 0) : OGroup R :=
  reflOf R (u + z) hau * reflOf R (v + z) hbv

theorem k3Sig_actions (hzu : polar R z u = 0) (hzv : polar R z v = 0)
    (huv : polar R u v = 0) (hz : R z = R u) (huv' : R u = R v) (hne : R u ≠ 0)
    (hau : R (u + z) ≠ 0) (hbv : R (v + z) ≠ 0) :
    ((k3Sig z u v hau hbv : OGroup R) : W ≃ₗ[ZMod 3] W) z = -v ∧
      ((k3Sig z u v hau hbv : OGroup R) : W ≃ₗ[ZMod 3] W) u = -z ∧
      ((k3Sig z u v hau hbv : OGroup R) : W ≃ₗ[ZMod 3] W) v = u := by
  have hv : R v ≠ 0 := huv' ▸ hne
  have hp_uz : polar R u z = 0 := (QuadraticMap.polar_comm R u z).trans hzu
  have hp_vz : polar R v z = 0 := (QuadraticMap.polar_comm R v z).trans hzv
  have hp_vu : polar R v u = 0 := (QuadraticMap.polar_comm R v u).trans huv
  have hRay : R (u + z) = 2 * R u := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hp_uz, add_zero, hz]
    ring
  have hRbv : R (v + z) = 2 * R u := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hp_vz, add_zero, ← huv', ← hz]
    ring
  have hratio : (2 * R u) / (2 * R u) = 1 :=
    div_self (mul_ne_zero (by decide) hne)
  have hp_az : polar R (u + z) z = 2 * R u := by
    rw [QuadraticMap.polar_add_left, hp_uz, QuadraticMap.polar_self, nsmul_eq_mul, zero_add, hz]
    norm_num
  have hp_au : polar R (u + z) u = 2 * R u := by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_self, nsmul_eq_mul, hzu, add_zero]
    norm_num
  have hp_av : polar R (u + z) v = 0 := by
    rw [QuadraticMap.polar_add_left, huv, hzv, add_zero]
  have hp_bz : polar R (v + z) z = 2 * R u := by
    rw [QuadraticMap.polar_add_left, hp_vz, QuadraticMap.polar_self, nsmul_eq_mul, zero_add, hz]
    norm_num
  have hp_bu : polar R (v + z) u = 0 := by
    rw [QuadraticMap.polar_add_left, hp_vu, hzu, add_zero]
  have hp_bv : polar R (v + z) v = 2 * R u := by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_self, nsmul_eq_mul, hzv, add_zero,
      ← huv']
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [k3Sig, Subgroup.coe_mul, LinearEquiv.mul_apply]
    have hb_z : ((reflOf R (v + z) hbv : OGroup R) : W ≃ₗ[ZMod 3] W) z = -v := by
      rw [coe_reflOf_apply (v + z) hbv z, hp_bz, hRbv, hratio, one_smul]
      abel
    rw [hb_z, map_neg, coe_reflOf_apply (u + z) hau v, hp_av, zero_div, zero_smul, sub_zero]
  · rw [k3Sig, Subgroup.coe_mul, LinearEquiv.mul_apply]
    have hb_u : ((reflOf R (v + z) hbv : OGroup R) : W ≃ₗ[ZMod 3] W) u = u := by
      rw [coe_reflOf_apply (v + z) hbv u, hp_bu, zero_div, zero_smul, sub_zero]
    rw [hb_u, coe_reflOf_apply (u + z) hau u, hp_au, hRay, hratio, one_smul]
    abel
  · rw [k3Sig, Subgroup.coe_mul, LinearEquiv.mul_apply]
    have hb_v : ((reflOf R (v + z) hbv : OGroup R) : W ≃ₗ[ZMod 3] W) v = -z := by
      rw [coe_reflOf_apply (v + z) hbv v, hp_bv, hRbv, hratio, one_smul]
      abel
    rw [hb_v, map_neg, coe_reflOf_apply (u + z) hau z, hp_az, hRay, hratio, one_smul]
    abel

theorem k3_sig_cube (hdim : Module.finrank (ZMod 3) W = 3)
    (hzu : polar R z u = 0) (hzv : polar R z v = 0) (huv : polar R u v = 0)
    (hz : R z = R u) (huv' : R u = R v) (hne : R u ≠ 0)
    (hau : R (u + z) ≠ 0) (hbv : R (v + z) ≠ 0) :
    (k3Sig z u v hau hbv) ^ 3 = 1 := by
  obtain ⟨hz', hu', hv'⟩ := k3Sig_actions z u v hzu hzv huv hz huv' hne hau hbv
  have hcube : ((k3Sig z u v hau hbv : OGroup R) : W ≃ₗ[ZMod 3] W) ^ 3 = 1 := by
    apply k3_ext z u v hdim hzu hzv huv hz huv' hne
    · show (((k3Sig z u v hau hbv : OGroup R) : W ≃ₗ[ZMod 3] W) ^ 3) z = z
      simp only [pow_three, LinearEquiv.mul_apply, hz', hu', hv', map_neg, neg_neg]
    · show (((k3Sig z u v hau hbv : OGroup R) : W ≃ₗ[ZMod 3] W) ^ 3) u = u
      simp only [pow_three, LinearEquiv.mul_apply, hz', hu', hv', map_neg, neg_neg]
    · show (((k3Sig z u v hau hbv : OGroup R) : W ≃ₗ[ZMod 3] W) ^ 3) v = v
      simp only [pow_three, LinearEquiv.mul_apply, hz', hu', hv', map_neg, neg_neg]
  apply Subtype.ext
  simpa using hcube

end SigCube
end CFSG.OddStandard.SmallF3.Omega
