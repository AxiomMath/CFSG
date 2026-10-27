module

public import CFSG.ClassicalInvolution.Q3.TL4MF163PGL
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.GorensteinWalter Matrix.ProjGenLinGroup CFSG.ClassicalInvolution.Q3.TL4.MF163

variable {K : Type} [Field K]

@[expose] def dm (a : Kˣ) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : K), 0; 0, 1] (by simp [Matrix.det_fin_two_of])

@[expose] def wm : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : K), 1; 1, 0] (by simp [Matrix.det_fin_two_of])

theorem coe_dm (a : Kˣ) :
    ((dm a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, 1] := by
  simp [dm]

theorem coe_wm : ((wm : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![(0 : K), 1; 1, 0] := by
  simp [wm]

theorem dm_mul (a b : Kˣ) : dm (a * b) = dm a * dm b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dm, Matrix.mul_apply, Fin.sum_univ_two]

theorem dm_one : dm (1 : Kˣ) = (1 : GL (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dm]

theorem wm_mul_wm : (wm : GL (Fin 2) K) * wm = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_wm, Matrix.mul_apply, Fin.sum_univ_two]

theorem wm_mul_dm (a : Kˣ) :
    (wm : GL (Fin 2) K) * dm a = Matrix.GeneralLinearGroup.scalar (Fin 2) a * dm a⁻¹ * wm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dm, coe_wm, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.scalar_apply]

@[expose] def dmHom : Kˣ →* GL (Fin 2) K where
  toFun := dm
  map_one' := dm_one
  map_mul' := dm_mul

@[expose] noncomputable def tor : Kˣ →* PGammaL2 K :=
  (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).comp ((Matrix.ProjGenLinGroup.mk).comp dmHom)

@[expose] noncomputable def wref : PGammaL2 K :=
  SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk (wm : GL (Fin 2) K))

theorem tor_apply (a : Kˣ) :
    (tor a : PGammaL2 K) = SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk (dm a)) := rfl

theorem wref_mul_wref : (wref : PGammaL2 K) * wref = 1 := by
  rw [wref, ← map_mul, ← map_mul, wm_mul_wm, map_one, map_one]

theorem wref_mul_tor (a : Kˣ) : (wref : PGammaL2 K) * tor a = tor a⁻¹ * wref := by
  rw [wref, tor_apply, tor_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul, wm_mul_dm]
  simp only [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

@[expose] def umap (σ : K ≃+* K) : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom

theorem coe_umap (σ : K ≃+* K) (a : Kˣ) : ((umap σ a : Kˣ) : K) = σ (a : K) := rfl

theorem pgl2FieldAut_mk_dm (σ : K ≃+* K) (a : Kˣ) :
    pgl2FieldAut K σ (Matrix.ProjGenLinGroup.mk (dm a)) =
      Matrix.ProjGenLinGroup.mk (dm (umap σ a)) := by
  show pgl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (dm a)) = _
  rw [pgl2RingEquiv_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dm, coe_umap, Matrix.GeneralLinearGroup.map]

theorem pgl2FieldAut_mk_wm (σ : K ≃+* K) :
    pgl2FieldAut K σ (Matrix.ProjGenLinGroup.mk (wm : GL (Fin 2) K)) =
      Matrix.ProjGenLinGroup.mk (wm : GL (Fin 2) K) := by
  show pgl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) wm) = _
  rw [pgl2RingEquiv_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_wm, Matrix.GeneralLinearGroup.map]

theorem inr_mul_inl_eq (σ : K ≃+* K) (n : PGL2 K) :
    (SemidirectProduct.inr σ : PGammaL2 K) * SemidirectProduct.inl n =
      SemidirectProduct.inl (pgl2FieldAut K σ n) * SemidirectProduct.inr σ := by
  rw [SemidirectProduct.inl_aut, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

theorem inr_mul_tor (σ : K ≃+* K) (a : Kˣ) :
    (SemidirectProduct.inr σ : PGammaL2 K) * tor a = tor (umap σ a) * SemidirectProduct.inr σ := by
  rw [tor_apply, tor_apply, inr_mul_inl_eq, pgl2FieldAut_mk_dm]

theorem inr_mul_wref (σ : K ≃+* K) :
    (SemidirectProduct.inr σ : PGammaL2 K) * wref = wref * SemidirectProduct.inr σ := by
  rw [wref, inr_mul_inl_eq, pgl2FieldAut_mk_wm]

theorem tor_injective : Function.Injective (tor : Kˣ →* PGammaL2 K) := by
  intro a a' h
  rw [tor_apply, tor_apply, SemidirectProduct.inl_inj, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  have h11 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 1 1) hu
  have h00 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) hu
  simp [coe_dm, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.scalar_apply] at h11 h00
  subst h11
  exact Units.ext (by simpa using h00)

theorem pgl2_comm_dm_neg_one (h2 : (2 : K) ≠ 0) {A : PGL2 K}
    (hA : A * Matrix.ProjGenLinGroup.mk (dm (-1)) = Matrix.ProjGenLinGroup.mk (dm (-1)) * A) :
    ∃ (β : Kˣ) (ε : ℕ), ε ≤ 1 ∧ A = Matrix.ProjGenLinGroup.mk (dm β) *
      (Matrix.ProjGenLinGroup.mk (wm : GL (Fin 2) K)) ^ ε := by
  induction A using Matrix.ProjGenLinGroup.induction_on with | mk M => ?_
  rw [← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hA
  obtain ⟨u, hu⟩ := hA
  have hdet := det_ne_zero_of_GL M
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrArg (fun N : GL (Fin 2) K => (N : Matrix (Fin 2) (Fin 2) K) 0 0) hu
  have e01 := congrArg (fun N : GL (Fin 2) K => (N : Matrix (Fin 2) (Fin 2) K) 0 1) hu
  have e10 := congrArg (fun N : GL (Fin 2) K => (N : Matrix (Fin 2) (Fin 2) K) 1 0) hu
  have e11 := congrArg (fun N : GL (Fin 2) K => (N : Matrix (Fin 2) (Fin 2) K) 1 1) hu
  simp [coe_dm, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.scalar_apply] at e00 e01 e10 e11
  set a := (M : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set b := (M : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  set c := (M : Matrix (Fin 2) (Fin 2) K) 1 0 with hc
  set d := (M : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  have hMe : (M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  by_cases hu1 : (u : K) = 1
  ·
    have hb0 : b = 0 := by
      rw [hu1] at e01
      have : (2 : K) * b = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_left h2
    have hc0 : c = 0 := by
      rw [hu1] at e10
      have : (2 : K) * c = 0 := by linear_combination -e10
      exact (mul_eq_zero.mp this).resolve_left h2
    have hd0 : d ≠ 0 := by
      intro h; apply hdet; rw [h, hb0, hc0]; ring
    have ha0 : a ≠ 0 := by
      intro h; apply hdet; rw [h, hb0, hc0]; ring
    refine ⟨Units.mk0 (a / d) (div_ne_zero ha0 hd0), 0, by norm_num, ?_⟩
    rw [pow_zero, mul_one]
    refine mk_eq_mk_of_smul hd0 ?_
    rw [hMe, coe_dm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb0, hc0] <;> field_simp
  · by_cases hum : (u : K) = -1
    ·
      have ha0' : a = 0 := by
        rw [hum] at e00
        have : (2 : K) * a = 0 := by linear_combination -e00
        exact (mul_eq_zero.mp this).resolve_left h2
      have hd0' : d = 0 := by
        rw [hum] at e11
        have : (2 : K) * d = 0 := by linear_combination -e11
        exact (mul_eq_zero.mp this).resolve_left h2
      have hb0 : b ≠ 0 := by
        intro h; apply hdet; rw [h, ha0', hd0']; ring
      have hc0 : c ≠ 0 := by
        intro h; apply hdet; rw [h, ha0', hd0']; ring
      refine ⟨Units.mk0 (b / c) (div_ne_zero hb0 hc0), 1, le_rfl, ?_⟩
      rw [pow_one, ← map_mul]
      refine mk_eq_mk_of_smul hc0 ?_
      rw [hMe, Units.val_mul, coe_dm, coe_wm]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha0', hd0', Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp
    · exfalso
      have h1 : (u : K) - 1 ≠ 0 := fun h => hu1 (by linear_combination h)
      have h2' : (u : K) + 1 ≠ 0 := fun h => hum (by linear_combination h)
      have ha0 : a = 0 := by
        have : a * ((u : K) - 1) = 0 := by linear_combination e00
        exact (mul_eq_zero.mp this).resolve_right h1
      have hd0 : d = 0 := by
        have : d * ((u : K) - 1) = 0 := by linear_combination e11
        exact (mul_eq_zero.mp this).resolve_right h1
      have hb0 : b = 0 := by
        have : b * ((u : K) + 1) = 0 := by linear_combination e01
        exact (mul_eq_zero.mp this).resolve_right h2'
      apply hdet
      rw [ha0, hb0]
      ring

theorem umap_neg_one (σ : K ≃+* K) : umap σ (-1) = -1 :=
  Units.ext (by simp [coe_umap])

theorem exists_decomp (h2 : (2 : K) ≠ 0) {g : PGammaL2 K} (hg : g * tor (-1) = tor (-1) * g) :
    ∃ (γ : Kˣ) (ε : ℕ) (σ : K ≃+* K), ε ≤ 1 ∧
      g = tor γ * wref ^ ε * SemidirectProduct.inr σ := by
  have hg' := SemidirectProduct.inl_left_mul_inr_right g
  have hZ : (tor (-1) : PGammaL2 K) = SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk (dm (-1))) :=
    tor_apply _
  have hσZ : pgl2FieldAut K g.right (Matrix.ProjGenLinGroup.mk (dm (-1))) =
      Matrix.ProjGenLinGroup.mk (dm (-1)) := by
    rw [pgl2FieldAut_mk_dm, umap_neg_one]
  have h1 : g * tor (-1) = SemidirectProduct.inl (g.left * Matrix.ProjGenLinGroup.mk (dm (-1))) *
      SemidirectProduct.inr g.right := by
    calc g * tor (-1) = (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right) *
          SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk (dm (-1))) := by rw [hg', hZ]
      _ = SemidirectProduct.inl g.left * (SemidirectProduct.inr g.right *
          SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk (dm (-1)))) := by rw [mul_assoc]
      _ = SemidirectProduct.inl g.left * (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk (dm (-1))) *
          SemidirectProduct.inr g.right) := by rw [inr_mul_inl_eq, hσZ]
      _ = _ := by rw [← mul_assoc, ← map_mul]
  have h2' : tor (-1) * g = SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk (dm (-1)) * g.left) *
      SemidirectProduct.inr g.right := by
    calc tor (-1) * g = SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk (dm (-1))) *
          (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right) := by rw [hg', hZ]
      _ = _ := by rw [← mul_assoc, ← map_mul]
  rw [h1, h2'] at hg
  have hA := SemidirectProduct.inl_injective (mul_right_cancel hg)
  obtain ⟨β, ε, hε, hAe⟩ := pgl2_comm_dm_neg_one h2 hA
  refine ⟨β, ε, g.right, hε, ?_⟩
  calc g = SemidirectProduct.inl g.left * SemidirectProduct.inr g.right := hg'.symm
    _ = _ := by
      rw [hAe, map_mul, map_pow, tor_apply, wref, mul_assoc]

instance finite_pgammaL2 [Finite K] : Finite (PGammaL2 K) := by
  haveI : Finite (PGL2 K) := Finite.of_surjective
    (Matrix.ProjGenLinGroup.mk : GL (Fin 2) K → PGL2 K) Matrix.ProjGenLinGroup.mk_surjective
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  exact Finite.of_equiv (PGL2 K × (K ≃+* K)) SemidirectProduct.equivProd.symm

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
