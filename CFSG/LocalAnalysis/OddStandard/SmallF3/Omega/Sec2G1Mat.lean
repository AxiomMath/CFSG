module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Open

theorem eq_one_or_eq_neg_one_of_mul_self_eq_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : A * A = 1) (hd : A.det = 1) : A = 1 ∨ A = -1 := by
  have h00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    have h := congrFun (congrFun hA 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have h01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by
    have h := congrFun (congrFun hA 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have h10 : A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0 := by
    have h := congrFun (congrFun hA 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have h11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = 1 := by
    have h := congrFun (congrFun hA 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [Matrix.det_fin_two A] at hd
    exact hd
  by_cases hsum : A 0 0 + A 1 1 = 0
  · exfalso
    have hzero : (0 : K) = 2 := by
      linear_combination h00 + hdet - (A 0 0) * hsum
    exact h2 hzero.symm
  · have hb : A 0 1 = 0 := by
      have h : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.mp h).resolve_right hsum
    have hc : A 1 0 = 0 := by
      have h : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.mp h).resolve_right hsum
    have haa : A 0 0 * A 0 0 = 1 := by
      have h := h00
      rw [hb, hc, mul_zero, add_zero] at h
      exact h
    have had : A 0 0 * A 1 1 = 1 := by
      have h := hdet
      rw [hb, zero_mul, sub_zero] at h
      exact h
    have hane : A 0 0 ≠ 0 := by
      intro h
      rw [h, mul_zero] at haa
      exact one_ne_zero haa.symm
    have hda : A 1 1 = A 0 0 := by
      have h : A 0 0 * A 0 0 = A 0 0 * A 1 1 := by rw [haa, had]
      exact (mul_left_cancel₀ hane h).symm
    rcases mul_self_eq_one_iff.mp haa with ha | ha
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hda, hb, hc]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hda, hb, hc]

private theorem mul_self_eq_one_of_relations {G : Type} [Group G] {q r z1 z2 : G}
    (hz1 : ∀ y, z1 * y = y * z1) (hz2 : ∀ y, z2 * y = y * z2) (hz2sq : z2 * z2 = 1)
    (hqr : q * q = (r * r) * z1) (hrq : r * q * r⁻¹ = q⁻¹ * z2) :
    (q * q) * (q * q) = 1 := by
  have hconj : r * (q * q) * r⁻¹ = q * q := by
    calc r * (q * q) * r⁻¹
        = r * ((r * r) * z1) * r⁻¹ := by rw [hqr]
      _ = (r * (r * r) * r⁻¹) * (r * z1 * r⁻¹) := by group
      _ = r * r * z1 := by
            rw [show r * (r * r) * r⁻¹ = r * r from by group,
                show r * z1 * r⁻¹ = z1 from by rw [← hz1 r]; group]
      _ = q * q := hqr.symm
  have hconj2 : r * (q * q) * r⁻¹ = (q * q)⁻¹ * (z2 * z2) := by
    have hsq : r * (q * q) * r⁻¹ = (q⁻¹ * z2) * (q⁻¹ * z2) := by
      calc r * (q * q) * r⁻¹
          = (r * q * r⁻¹) * (r * q * r⁻¹) := by group
        _ = (q⁻¹ * z2) * (q⁻¹ * z2) := by rw [hrq]
    rw [hsq]
    calc (q⁻¹ * z2) * (q⁻¹ * z2)
        = q⁻¹ * (z2 * q⁻¹) * z2 := by group
      _ = q⁻¹ * (q⁻¹ * z2) * z2 := by rw [hz2 q⁻¹]
      _ = (q * q)⁻¹ * (z2 * z2) := by group
  have hseq : q * q = (q * q)⁻¹ := by
    have h := hconj.symm.trans hconj2
    rw [hz2sq, mul_one] at h
    exact h
  exact (mul_eq_one_iff_eq_inv).mpr hseq

private theorem exists_scalar_mul_of_statedProj_eq {K : Type} [Field K]
    {H : Subgroup (GL (Fin 2) K)} {x y : H}
    (h : (x : StatedProj H) = (y : StatedProj H)) :
    ∃ u : Kˣ, (y : GL (Fin 2) K) = (x : GL (Fin 2) K) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  classical
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff H x y).mp h
  exact ⟨u, Units.ext (by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal] using hu)⟩

theorem not_injective_quaternion_statedProj {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    (f : QuaternionGroup 2 →* StatedProj (StatedSL 2 K)) : ¬ Function.Injective f := by
  classical
  intro hinj
  let H : Subgroup (GL (Fin 2) K) := StatedSL 2 K
  have ha1sq : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide +kernel
  have hxa0sq : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by decide +kernel
  have hconjQ : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 *
      (QuaternionGroup.xa 0)⁻¹ = (QuaternionGroup.a 1)⁻¹ := by decide +kernel
  have ha2ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide +kernel
  obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective ((StatedScalars (Fin 2) K).subgroupOf H)
    (f (QuaternionGroup.a 1))
  obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective ((StatedScalars (Fin 2) K).subgroupOf H)
    (f (QuaternionGroup.xa 0))
  have hq' : (q : StatedProj H) = f (QuaternionGroup.a 1) := hq
  have hr' : (r : StatedProj H) = f (QuaternionGroup.xa 0) := hr
  have hqq : ((q * q : H) : StatedProj H) = ((r * r : H) : StatedProj H) := by
    calc ((q * q : H) : StatedProj H)
        = (q : StatedProj H) * (q : StatedProj H) := by rw [QuotientGroup.mk_mul]
      _ = f (QuaternionGroup.a 1) * f (QuaternionGroup.a 1) := by rw [hq']
      _ = f (QuaternionGroup.a 1 * QuaternionGroup.a 1) := (map_mul f _ _).symm
      _ = f (QuaternionGroup.xa 0 * QuaternionGroup.xa 0) := by rw [ha1sq, hxa0sq]
      _ = f (QuaternionGroup.xa 0) * f (QuaternionGroup.xa 0) := map_mul f _ _
      _ = (r : StatedProj H) * (r : StatedProj H) := by rw [hr']
      _ = ((r * r : H) : StatedProj H) := by rw [QuotientGroup.mk_mul]
  have hrq : ((r * q * r⁻¹ : H) : StatedProj H) = ((q⁻¹ : H) : StatedProj H) := by
    calc ((r * q * r⁻¹ : H) : StatedProj H)
        = (r : StatedProj H) * (q : StatedProj H) * (r : StatedProj H)⁻¹ := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = f (QuaternionGroup.xa 0) * f (QuaternionGroup.a 1) *
            (f (QuaternionGroup.xa 0))⁻¹ := by rw [hq', hr']
      _ = f (QuaternionGroup.xa 0 * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = f ((QuaternionGroup.a 1)⁻¹) := by rw [hconjQ]
      _ = (f (QuaternionGroup.a 1))⁻¹ := map_inv f _
      _ = (q : StatedProj H)⁻¹ := by rw [hq']
      _ = ((q⁻¹ : H) : StatedProj H) := by rw [QuotientGroup.mk_inv]
  obtain ⟨u1, hu1⟩ := exists_scalar_mul_of_statedProj_eq hqq.symm
  obtain ⟨u2, hu2⟩ := exists_scalar_mul_of_statedProj_eq hrq.symm
  have hdet_q : (q : GL (Fin 2) K).det = 1 := by
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using
      (CFSG.Open.StatedAPI.det_of_mem_statedSL (n := 2) (K := K) q.2)
  have hdet_r : (r : GL (Fin 2) K).det = 1 := by
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using
      (CFSG.Open.StatedAPI.det_of_mem_statedSL (n := 2) (K := K) r.2)
  have hA : (q : GL (Fin 2) K) * (q : GL (Fin 2) K) =
      ((r : GL (Fin 2) K) * (r : GL (Fin 2) K)) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) u1 := by
    have hqmul : ((q * q : H) : GL (Fin 2) K) =
        (q : GL (Fin 2) K) * (q : GL (Fin 2) K) := by simp only [Subgroup.coe_mul]
    have hrmul : ((r * r : H) : GL (Fin 2) K) =
        (r : GL (Fin 2) K) * (r : GL (Fin 2) K) := by simp only [Subgroup.coe_mul]
    rw [← hqmul, ← hrmul]
    exact hu1
  have hB : (r : GL (Fin 2) K) * (q : GL (Fin 2) K) * (r : GL (Fin 2) K)⁻¹ =
      (q : GL (Fin 2) K)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u2 := by
    have hrmul2 : ((r * q * r⁻¹ : H) : GL (Fin 2) K) =
        (r : GL (Fin 2) K) * (q : GL (Fin 2) K) * (r : GL (Fin 2) K)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hqinv : ((q⁻¹ : H) : GL (Fin 2) K) = (q : GL (Fin 2) K)⁻¹ := by
      simp only [Subgroup.coe_inv]
    rw [← hrmul2, ← hqinv]
    exact hu2
  have hz1 : ∀ y : GL (Fin 2) K, Matrix.GeneralLinearGroup.scalar (Fin 2) u1 * y =
      y * Matrix.GeneralLinearGroup.scalar (Fin 2) u1 :=
    fun y => Matrix.GeneralLinearGroup.scalar_commute u1 y
  have hz2 : ∀ y : GL (Fin 2) K, Matrix.GeneralLinearGroup.scalar (Fin 2) u2 * y =
      y * Matrix.GeneralLinearGroup.scalar (Fin 2) u2 :=
    fun y => Matrix.GeneralLinearGroup.scalar_commute u2 y
  have hdet_z2 : (Matrix.GeneralLinearGroup.scalar (Fin 2) u2).det = 1 := by
    have h := congrArg (Matrix.GeneralLinearGroup.det) hB
    simp only [map_mul, map_inv] at h
    rw [hdet_r, hdet_q] at h
    simpa using h.symm
  have hu2sq : u2 ^ 2 = 1 := by
    have h := hdet_z2
    rw [Matrix.GeneralLinearGroup.det_scalar] at h
    simpa using h
  have hzz : Matrix.GeneralLinearGroup.scalar (Fin 2) u2 *
      Matrix.GeneralLinearGroup.scalar (Fin 2) u2 = 1 := by
    rw [← map_mul, ← pow_two, hu2sq, map_one]
  have hs_mul : ((q : GL (Fin 2) K) * (q : GL (Fin 2) K)) *
      ((q : GL (Fin 2) K) * (q : GL (Fin 2) K)) = 1 :=
    mul_self_eq_one_of_relations hz1 hz2 hzz hA hB
  have hqmul : ((q * q : H) : GL (Fin 2) K) =
      (q : GL (Fin 2) K) * (q : GL (Fin 2) K) := by simp only [Subgroup.coe_mul]
  have hs_mul' : ((q * q : H) : GL (Fin 2) K) * ((q * q : H) : GL (Fin 2) K) = 1 := by
    rw [hqmul]
    exact hs_mul
  have hdet_s : ((((q * q : H) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL (n := 2) (K := K) (q * q).2
  have hs_mat_sq : ((((q * q : H) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) *
      ((((q * q : H) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have h := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hs_mul'
    simpa using h
  have hs_pm : ((((q * q : H) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
      ((((q * q : H) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) = -1 :=
    eq_one_or_eq_neg_one_of_mul_self_eq_one h2 hs_mat_sq hdet_s
  have hsZ : ((q * q : H) : GL (Fin 2) K) ∈ StatedScalars (Fin 2) K := by
    rw [StatedScalars, MonoidHom.mem_range]
    rcases hs_pm with hm | hm
    · exact ⟨1, by apply Units.ext; simpa [Matrix.GeneralLinearGroup.coe_scalar] using hm.symm⟩
    · refine ⟨-1, ?_⟩
      apply Units.ext
      have hscal : (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Kˣ) :
          Matrix (Fin 2) (Fin 2) K) = -1 := by
        rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Matrix.one_apply]
      rw [hscal]
      exact hm.symm
  have hmN : (q * q : H) ∈ (StatedScalars (Fin 2) K).subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hsZ
  have hcls : ((q * q : H) : StatedProj H) = 1 :=
    (QuotientGroup.eq_one_iff (q * q)).mpr hmN
  have hcls_a2 : ((q * q : H) : StatedProj H) = f (QuaternionGroup.a 2) := by
    calc ((q * q : H) : StatedProj H)
        = (q : StatedProj H) * (q : StatedProj H) := by rw [QuotientGroup.mk_mul]
      _ = f (QuaternionGroup.a 1) * f (QuaternionGroup.a 1) := by rw [hq']
      _ = f (QuaternionGroup.a 1 * QuaternionGroup.a 1) := (map_mul f _ _).symm
      _ = f (QuaternionGroup.a 2) := by rw [ha1sq]
  have hfa2 : f (QuaternionGroup.a 2) = 1 := hcls_a2 ▸ hcls
  exact ha2ne (hinj (by rw [hfa2, map_one]))

end CFSG.OddStandard.SmallF3.Omega
