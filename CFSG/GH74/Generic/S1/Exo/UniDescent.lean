module

public import CFSG.GH74.Generic.S1.Exo.Defs
public import CFSG.GH74.Generic.S1.Exo.UniDescentField
public import CFSG.GH74.Generic.S1.Exo.UniDescentAdj
public import CFSG.GH74.Generic.S1.Exo.UniDescentBasis

public section

namespace CFSG.GH74.Generic.S1.Exo

open scoped Matrix

section Core

variable {F : Type} [Field F]

@[expose] def uniDescLift (bar : F →+* F) (A : Matrix (Fin 4) (Fin 4) F) (hA : A.map bar = A) :
    Matrix (Fin 4) (Fin 4) (bar.eqLocusField (RingHom.id F)) :=
  Matrix.of fun i j => ⟨A i j, by
    have := congrFun (congrFun hA i) j
    simpa [RingHom.mem_eqLocusField] using this⟩

theorem uniDescLift_map (bar : F →+* F) (A : Matrix (Fin 4) (Fin 4) F) (hA : A.map bar = A) :
    (uniDescLift bar A hA).map (bar.eqLocusField (RingHom.id F)).subtype = A := by
  ext i j
  rfl

theorem uniDesc_exists_gl (bar : F →+* F) (Y : GL (Fin 4) F)
    (hY : Matrix.GeneralLinearGroup.map bar Y = Y) :
    ∃ x : GL (Fin 4) (bar.eqLocusField (RingHom.id F)),
      Matrix.GeneralLinearGroup.map (bar.eqLocusField (RingHom.id F)).subtype x = Y := by
  have hY' : Matrix.GeneralLinearGroup.map bar Y⁻¹ = Y⁻¹ := by rw [map_inv, hY]
  have h1 : (Y : Matrix (Fin 4) (Fin 4) F).map bar = Y := congrArg Units.val hY
  have h2 : ((Y⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar =
      (Y⁻¹ : GL (Fin 4) F) := congrArg Units.val hY'
  set ι := (bar.eqLocusField (RingHom.id F)).subtype with hι
  have hinj : ∀ A B : Matrix (Fin 4) (Fin 4) (bar.eqLocusField (RingHom.id F)),
      A.map ι = B.map ι → A = B := fun A B h =>
    Matrix.map_injective (Subfield.subtype_injective _) h
  refine ⟨⟨uniDescLift bar Y h1, uniDescLift bar (Y⁻¹ : GL (Fin 4) F) h2, ?_, ?_⟩, ?_⟩
  · apply hinj
    rw [Matrix.map_mul, uniDescLift_map, uniDescLift_map, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.map_one _ (map_zero ι) (map_one ι)]
  · apply hinj
    rw [Matrix.map_mul, uniDescLift_map, uniDescLift_map, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.map_one _ (map_zero ι) (map_one ι)]
  · apply Units.ext
    exact uniDescLift_map bar Y h1

theorem uniDesc_core {q : ℕ} (bar : F →+* F) (hbar : ∀ x, bar x = x ^ q)
    (hbb : ∀ x, bar (bar x) = x) (g P : GL (Fin 4) F)
    (hgP : g * Matrix.GeneralLinearGroup.map bar P = P)
    (G₀ : Matrix (Fin 4) (Fin 4) (bar.eqLocusField (RingHom.id F)))
    (hG₀ : G₀.map (bar.eqLocusField (RingHom.id F)).subtype =
      uniDescAdj bar (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F)) :
    ∃ ψ : uniFixed q bar g ≃* soMat G₀,
      ∀ k : uniFixed q bar g, (k : GL (Fin 4) F) = -1 →
        (ψ k : GL (Fin 4) (bar.eqLocusField (RingHom.id F))) = -1 := by
  set ι := (bar.eqLocusField (RingHom.id F)).subtype with hι
  have hmapinj : ∀ A B : Matrix (Fin 4) (Fin 4) (bar.eqLocusField (RingHom.id F)),
      A.map ι = B.map ι → A = B := fun A B h =>
    Matrix.map_injective (Subfield.subtype_injective _) h
  have hbarι : ∀ r : bar.eqLocusField (RingHom.id F), bar (ι r) = ι r := fun r => r.2
  let Ξ : GL (Fin 4) (bar.eqLocusField (RingHom.id F)) →* GL (Fin 4) F :=
    (MulAut.conj P).toMonoidHom.comp (Matrix.GeneralLinearGroup.map ι)
  have hΞ : ∀ x, Ξ x = P * Matrix.GeneralLinearGroup.map ι x * P⁻¹ := fun x => rfl
  have hΞmat : ∀ x, ((Ξ x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) _).map ι *
        ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := fun x => rfl
  have hPPi : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinj : Function.Injective Ξ := by
    intro x y hxy
    rw [hΞ, hΞ] at hxy
    have h1 : Matrix.GeneralLinearGroup.map ι x = Matrix.GeneralLinearGroup.map ι y :=
      mul_left_cancel (mul_right_cancel hxy)
    apply Units.ext
    exact Matrix.map_injective (Subfield.subtype_injective _) (congrArg Units.val h1)
  have hmap : (soMat G₀).map Ξ = uniFixed q bar g := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hx1, hx2⟩ := hx
      set Y : Matrix (Fin 4) (Fin 4) F := (x : Matrix (Fin 4) (Fin 4) _).map ι with hYdef
      have hY : Y.map bar = Y := by
        ext i j
        simp only [hYdef, Matrix.map_apply]
        exact hbarι _
      have hKP : ((Ξ x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * Y := by
        rw [hΞmat, Matrix.mul_assoc, Matrix.mul_assoc, hPiP, Matrix.mul_one]
      have hYG : Yᵀ * (uniDescAdj bar (P : Matrix (Fin 4) (Fin 4) F) *
            (P : Matrix (Fin 4) (Fin 4) F)) * Y =
          uniDescAdj bar (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) := by
        have := congrArg
          (fun M : Matrix (Fin 4) (Fin 4) (bar.eqLocusField (RingHom.id F)) => M.map ι) hx1
        simp only [Matrix.map_mul, hG₀] at this
        exact this
      have hsu := (uniDesc_adj_iff bar hPPi hKP hY).2 hYG
      have hdet : ((Ξ x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
        rw [hΞmat, Matrix.det_units_conj P Y]
        have h2 := RingHom.map_det ι (x : Matrix (Fin 4) (Fin 4) _)
        rw [hx2, map_one] at h2
        exact h2.symm
      refine ⟨(uniDesc_mem_statedSU_iff bar hbar hbb _).2 ⟨hdet, hsu⟩, ?_⟩
      have hbm : Matrix.GeneralLinearGroup.map bar (Matrix.GeneralLinearGroup.map ι x) =
          Matrix.GeneralLinearGroup.map ι x := Units.ext hY
      show g * Matrix.GeneralLinearGroup.map bar (Ξ x) * g⁻¹ = Ξ x
      rw [hΞ, map_mul, map_mul, map_inv, hbm]
      calc g * (Matrix.GeneralLinearGroup.map bar P * Matrix.GeneralLinearGroup.map ι x *
            (Matrix.GeneralLinearGroup.map bar P)⁻¹) * g⁻¹
          = (g * Matrix.GeneralLinearGroup.map bar P) * Matrix.GeneralLinearGroup.map ι x *
            (g * Matrix.GeneralLinearGroup.map bar P)⁻¹ := by group
        _ = P * Matrix.GeneralLinearGroup.map ι x * P⁻¹ := by rw [hgP]
    · intro hy
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨hydet, hysu⟩ := (uniDesc_mem_statedSU_iff bar hbar hbb y).1 hy1
      have hfix : g * Matrix.GeneralLinearGroup.map bar y * g⁻¹ = y := hy2
      have hmy : Matrix.GeneralLinearGroup.map bar y = g⁻¹ * y * g := by
        calc Matrix.GeneralLinearGroup.map bar y
            = g⁻¹ * (g * Matrix.GeneralLinearGroup.map bar y * g⁻¹) * g := by group
          _ = g⁻¹ * y * g := by rw [hfix]
      have hmP : Matrix.GeneralLinearGroup.map bar P = g⁻¹ * P := by
        calc Matrix.GeneralLinearGroup.map bar P
            = g⁻¹ * (g * Matrix.GeneralLinearGroup.map bar P) := by group
          _ = g⁻¹ * P := by rw [hgP]
      set Yg : GL (Fin 4) F := P⁻¹ * y * P with hYgdef
      have hYg : Matrix.GeneralLinearGroup.map bar Yg = Yg := by
        rw [hYgdef, map_mul, map_mul, map_inv, hmy, hmP]
        group
      obtain ⟨x, hx⟩ := uniDesc_exists_gl bar Yg hYg
      have hΞx : Ξ x = y := by
        rw [hΞ, hx, hYgdef]
        group
      refine ⟨x, ?_, hΞx⟩
      set Y : Matrix (Fin 4) (Fin 4) F := (Yg : Matrix (Fin 4) (Fin 4) F) with hYdef
      have hY : Y.map bar = Y := congrArg Units.val hYg
      have hxY : (x : Matrix (Fin 4) (Fin 4) _).map ι = Y := congrArg Units.val hx
      have hKP : (y : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
          (P : Matrix (Fin 4) (Fin 4) F) * Y := by
        rw [hYdef, ← Units.val_mul, ← Units.val_mul]
        congr 1
        rw [hYgdef]
        group
      have hYG := (uniDesc_adj_iff bar hPPi hKP hY).1 hysu
      refine ⟨?_, ?_⟩
      · apply hmapinj
        simp only [Matrix.map_mul]
        rw [hG₀, Matrix.transpose_map, hxY]
        exact hYG
      · apply (Subfield.subtype_injective _)
        have h2 := RingHom.map_det ι (x : Matrix (Fin 4) (Fin 4) _)
        have h3 : ι.mapMatrix (x : Matrix (Fin 4) (Fin 4) _) = Y := hxY
        rw [h3] at h2
        rw [h2, map_one]
        have h4 := Matrix.det_units_conj P⁻¹ (y : Matrix (Fin 4) (Fin 4) F)
        rw [inv_inv] at h4
        have h5 : Y = ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (y : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) := by
          rw [hYdef, hYgdef, Units.val_mul, Units.val_mul]
        rw [h5, h4, hydet]
  let e := (soMat G₀).equivMapOfInjective Ξ hinj
  let ψ : uniFixed q bar g ≃* soMat G₀ := (MulEquiv.subgroupCongr hmap.symm).trans e.symm
  have hψ : ∀ k : uniFixed q bar g, Ξ (ψ k : GL (Fin 4) (bar.eqLocusField (RingHom.id F))) =
      (k : GL (Fin 4) F) := by
    intro k
    have h1 := Subgroup.coe_equivMapOfInjective_apply (soMat G₀) Ξ hinj (ψ k)
    have h2 : e (ψ k) = MulEquiv.subgroupCongr hmap.symm k := by
      simp only [ψ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [← h1, h2]
    rfl
  refine ⟨ψ, fun k hk => ?_⟩
  apply hinj
  rw [hψ, hk, hΞ]
  have h1 : Matrix.GeneralLinearGroup.map ι
      (-1 : GL (Fin 4) (bar.eqLocusField (RingHom.id F))) = -1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.map]
  rw [h1]
  simp

theorem uniDesc_G0F_symm (bar : F →+* F) (g P : Matrix (Fin 4) (Fin 4) F) (hgs : gᵀ = g)
    (hP : g * P.map bar = P) :
    (uniDescAdj bar P * P)ᵀ = uniDescAdj bar P * P := by
  have h : uniDescAdj bar P * P = uniDescAdj bar P * g * P.map bar := by
    rw [Matrix.mul_assoc, hP]
  rw [h, Matrix.transpose_mul, Matrix.transpose_mul, uniDescAdj, Matrix.transpose_transpose, hgs,
    Matrix.mul_assoc]

theorem uniDesc_G0F_fix (bar : F →+* F) (hbb : ∀ x, bar (bar x) = x) (g P : Matrix (Fin 4) (Fin 4) F)
    (hgs : gᵀ = g) (hP : g * P.map bar = P) :
    (uniDescAdj bar P * P).map bar = uniDescAdj bar P * P := by
  have hsymm := uniDesc_G0F_symm bar g P hgs hP
  have h1 : (uniDescAdj bar P * P).map bar = (uniDescAdj bar P * P)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.map_mul, uniDescAdj, Matrix.transpose_transpose,
      ← Matrix.transpose_map]
    congr 2
    ext i j
    simp [hbb]
  rw [h1, hsymm]

theorem uniDesc_det_map (bar : F →+* F) (P : Matrix (Fin 4) (Fin 4) F) :
    (P.map bar).det = bar P.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

theorem uniDesc_not_isSquare {q : ℕ} (bar : F →+* F) (hbar : ∀ x, bar x = x ^ q)
    (hbb : ∀ x, bar (bar x) = x) (g : GL (Fin 4) F) (P : Matrix (Fin 4) (Fin 4) F)
    (hPu : IsUnit P.det) (hP : (g : Matrix (Fin 4) (Fin 4) F) * P.map bar = P)
    (hdet : ¬ ∃ u : F, u ^ (q + 1) = 1 ∧ u * u = (g : Matrix (Fin 4) (Fin 4) F).det)
    (G₀ : Matrix (Fin 4) (Fin 4) (bar.eqLocusField (RingHom.id F)))
    (hG₀ : G₀.map (bar.eqLocusField (RingHom.id F)).subtype = uniDescAdj bar P * P) :
    ¬ IsSquare G₀.det := by
  rintro ⟨r, hr⟩
  set ι := (bar.eqLocusField (RingHom.id F)).subtype with hι
  have hu0 : P.det ≠ 0 := hPu.ne_zero
  have hbu0 : bar P.det ≠ 0 := (map_ne_zero bar).2 hu0
  have hdetG : ι G₀.det = bar P.det * P.det := by
    rw [RingHom.map_det]
    have : ι.mapMatrix G₀ = uniDescAdj bar P * P := hG₀
    rw [this, Matrix.det_mul, uniDescAdj, Matrix.det_transpose, uniDesc_det_map]
  have hdetP : P.det = (g : Matrix (Fin 4) (Fin 4) F).det * bar P.det := by
    have h := congrArg Matrix.det hP
    rw [Matrix.det_mul, uniDesc_det_map] at h
    exact h.symm
  have hbt : bar (r : F) = r := r.2
  have htt : (r : F) * r = bar P.det * P.det := by
    rw [← hdetG, hr, map_mul]
    rfl
  refine hdet ⟨(r : F) / bar P.det, ?_, ?_⟩
  · rw [pow_succ, ← hbar, map_div₀, hbt, hbb]
    field_simp
    linear_combination htt
  · field_simp
    linear_combination htt + bar P.det * hdetP

end Core

theorem uniFixed_mulEquiv_soMat {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (bar : F →+* F) (hbar : ∀ x, bar x = x ^ q)
    (g : GL (Fin 4) F) (hgs : (g : Matrix (Fin 4) (Fin 4) F)ᵀ = (g : Matrix (Fin 4) (Fin 4) F))
    (hgu : ((g : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ * (g : Matrix (Fin 4) (Fin 4) F) = 1)
    (hdet : ¬ ∃ u : F, u ^ (q + 1) = 1 ∧ u * u = (g : Matrix (Fin 4) (Fin 4) F).det) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (G₀ : Matrix (Fin 4) (Fin 4) K₀),
      Nat.card K₀ = q ∧ G₀ᵀ = G₀ ∧ ¬ IsSquare G₀.det ∧
      ∃ ψ : uniFixed q bar g ≃* soMat G₀,
        ∀ k : uniFixed q bar g, (k : GL (Fin 4) F) = -1 → (ψ k : GL (Fin 4) K₀) = -1 := by
  obtain ⟨hbb, h2, ⟨δ, hδ0, hδ⟩, hcard⟩ := uniDesc_field_facts hF hq bar hbar
  have hgg : (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F).map bar = 1 := by
    have h1 : ((g : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ =
        (g : Matrix (Fin 4) (Fin 4) F).map bar := by
      rw [← Matrix.transpose_map, hgs]
    rw [h1] at hgu
    exact mul_eq_one_comm.1 hgu
  obtain ⟨P, hPu, hP⟩ := uniDesc_exists_P bar hbb h2 hδ0 hδ _ hgg
  let Pg : GL (Fin 4) F := Matrix.nonsingInvUnit P hPu
  have hgP : g * Matrix.GeneralLinearGroup.map bar Pg = Pg := Units.ext hP
  have hfix := uniDesc_G0F_fix bar hbb _ P hgs hP
  have hG₀ := uniDescLift_map bar (uniDescAdj bar P * P) hfix
  refine ⟨_, inferInstance, inferInstance, uniDescLift bar (uniDescAdj bar P * P) hfix, hcard, ?_,
    uniDesc_not_isSquare bar hbar hbb g P hPu hP hdet _ hG₀, ?_⟩
  · have hinj : ∀ A B : Matrix (Fin 4) (Fin 4) (bar.eqLocusField (RingHom.id F)),
        A.map (bar.eqLocusField (RingHom.id F)).subtype =
          B.map (bar.eqLocusField (RingHom.id F)).subtype → A = B := fun A B h =>
      Matrix.map_injective (Subfield.subtype_injective _) h
    apply hinj
    rw [Matrix.transpose_map, hG₀]
    exact uniDesc_G0F_symm bar _ P hgs hP
  · exact uniDesc_core bar hbar hbb g Pg hgP _ hG₀

end CFSG.GH74.Generic.S1.Exo
