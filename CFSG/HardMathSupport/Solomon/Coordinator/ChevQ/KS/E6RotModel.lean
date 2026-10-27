module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6RotDefs
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

@[expose] noncomputable def diagGL {F : Type} [Field F] : (Fin 3 → Fˣ) →* GL (Fin 3) F :=
  (Units.map (Matrix.diagonalRingHom (Fin 3) F).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin 3 => F)).symm.toMonoidHom

theorem coe_diagGL {F : Type} [Field F] (x : Fin 3 → Fˣ) :
    ((diagGL x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun k => (x k : F)) :=
  rfl

theorem diagGL_mem_SU {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) {x : Fin 3 → Fˣ}
    (hx : ∀ k, x k ^ 9 = 1) (hdet : x 0 * x 1 * x 2 = 1) : diagGL x ∈ unitarySU 2 3 F 3 := by
  have hx' : ∀ k, (x k : F) ^ 9 = 1 := fun k => by
    rw [← Units.val_pow_eq_pow_val, hx k, Units.val_one]
  rw [mem_unitarySU_iff h, coe_diagGL, Matrix.det_diagonal, Fin.prod_univ_three]
  refine ⟨?_, ?_⟩
  · simpa only [Units.val_mul, Units.val_one] using congrArg Units.val hdet
  · have hfun : (fun k => h.bar (x k : F) * (x k : F)) = 1 := by
      funext k
      show h.bar (x k : F) * (x k : F) = 1
      rw [h.bar_apply, show (2 : ℕ) ^ 3 = 8 by norm_num, ← pow_succ]
      exact hx' k
    rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, hfun]
    exact Matrix.diagonal_one

theorem glAut_diagGL {F : Type} [Field F] (σ : F ≃+* F) (x : Fin 3 → Fˣ) :
    glAut σ (diagGL x) = diagGL (fun k => Units.map (σ : F →* F) (x k)) := by
  apply Units.ext
  rw [coe_glAut, coe_diagGL, coe_diagGL, Matrix.diagonal_map (map_zero σ)]
  congr 1

theorem diagGL_eq_scalar {F : Type} [Field F] {x : Fin 3 → Fˣ} {c : Fˣ}
    (hx : diagGL x = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    x 0 = c ∧ x 1 = c ∧ x 2 = c := by
  have hm : Matrix.diagonal (fun k => (x k : F)) = Matrix.scalar (Fin 3) (c : F) := by
    rw [← coe_diagGL, hx, Matrix.GeneralLinearGroup.coe_scalar]
  have key : ∀ k, (x k : F) = (c : F) := fun k => by
    have hk := congrFun (congrFun hm k) k
    simpa [Matrix.scalar_apply] using hk
  exact ⟨Units.ext (key 0), Units.ext (key 1), Units.ext (key 2)⟩

theorem exists_orderOf_nine {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) :
    ∃ ζ : Fˣ, orderOf ζ = 9 := by
  have := h.finite
  have hcard : Nat.card Fˣ = 63 := by
    rw [Nat.card_units, h.card]
    norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have h7 : (7 : ℕ) ∣ orderOf g := by
    rw [hg, hcard]
    norm_num
  refine ⟨g ^ 7, ?_⟩
  rw [orderOf_pow_of_dvd (by norm_num) h7, hg, hcard]

theorem pow_nine_eq_one {F : Type} [Field F] {ζ : Fˣ} (hζ : orderOf ζ = 9) : ζ ^ 9 = 1 := by
  rw [← hζ]
  exact pow_orderOf_eq_one ζ

@[expose] noncomputable def torusGen₁ {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (ζ : Fˣ) (hζ : orderOf ζ = 9) : unitarySU 2 3 F 3 :=
  ⟨diagGL ![ζ, ζ⁻¹, 1], diagGL_mem_SU h (x := ![ζ, ζ⁻¹, 1])
    (fun k => by fin_cases k <;> simp [pow_nine_eq_one hζ, inv_pow]) (by simp)⟩

@[expose] noncomputable def torusGen₂ {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (ζ : Fˣ) (hζ : orderOf ζ = 9) : unitarySU 2 3 F 3 :=
  ⟨diagGL ![1, ζ, ζ⁻¹], diagGL_mem_SU h (x := ![1, ζ, ζ⁻¹])
    (fun k => by fin_cases k <;> simp [pow_nine_eq_one hζ, inv_pow]) (by simp)⟩

@[expose] def swapMat {F : Type} [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem swapMat_mul_self {F : Type} [Field F] :
    (swapMat : Matrix (Fin 3) (Fin 3) F) * swapMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem swapMat_map {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) :
    (swapMat : Matrix (Fin 3) (Fin 3) F).map h.bar = swapMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem swapMat_transpose {F : Type} [Field F] :
    (swapMat : Matrix (Fin 3) (Fin 3) F).transpose = swapMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

@[expose] noncomputable def swapGL {F : Type} [Field F] : GL (Fin 3) F :=
  Units.mk swapMat swapMat swapMat_mul_self swapMat_mul_self

theorem coe_swapGL {F : Type} [Field F] :
    ((swapGL : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = swapMat :=
  rfl

theorem swapGL_mem_SU {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) :
    swapGL ∈ unitarySU 2 3 F 3 := by
  have hc : CharP F 2 := h.charP
  have hneg : (-1 : F) = 1 := CharTwo.neg_eq 1
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [coe_swapGL, Matrix.det_fin_three]
    simp [swapMat, hneg]
  · rw [coe_swapGL, swapMat_map h, swapMat_transpose, swapMat_mul_self]

@[expose] noncomputable def swapEl {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) :
    unitarySU 2 3 F 3 :=
  ⟨swapGL, swapGL_mem_SU h⟩

theorem coe_torusGen₁ {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (ζ : Fˣ)
    (hζ : orderOf ζ = 9) :
    ((torusGen₁ h ζ hζ : unitarySU 2 3 F 3) : GL (Fin 3) F) = diagGL ![ζ, ζ⁻¹, 1] :=
  rfl

theorem coe_torusGen₂ {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (ζ : Fˣ)
    (hζ : orderOf ζ = 9) :
    ((torusGen₂ h ζ hζ : unitarySU 2 3 F 3) : GL (Fin 3) F) = diagGL ![1, ζ, ζ⁻¹] :=
  rfl

theorem coe_swapEl {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) :
    ((swapEl h : unitarySU 2 3 F 3) : GL (Fin 3) F) = swapGL :=
  rfl

theorem glAut_swapGL {F : Type} [Field F] (σ : F ≃+* F) : glAut σ swapGL = swapGL := by
  apply Units.ext
  rw [coe_glAut, coe_swapGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem torusGen_comm {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (ζ : Fˣ)
    (hζ : orderOf ζ = 9) :
    torusGen₁ h ζ hζ * torusGen₂ h ζ hζ = torusGen₂ h ζ hζ * torusGen₁ h ζ hζ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_torusGen₁, coe_torusGen₂, ← map_mul, ← map_mul]
  congr 1
  exact mul_comm _ _

theorem torusGen_indep {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (ζ : Fˣ)
    (hζ : orderOf ζ = 9) (i j : ℤ)
    (hc : torusGen₁ h ζ hζ ^ i * torusGen₂ h ζ hζ ^ j ∈
      Subgroup.center (unitarySU 2 3 F 3)) : (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
  rw [center_unitarySU_three (h := h) (by norm_num), mem_unitaryScalars] at hc
  obtain ⟨c, -, -, hc⟩ := hc
  have hval : ((torusGen₁ h ζ hζ ^ i * torusGen₂ h ζ hζ ^ j : unitarySU 2 3 F 3) :
      GL (Fin 3) F) = diagGL (![ζ, ζ⁻¹, 1] ^ i * ![1, ζ, ζ⁻¹] ^ j) := by
    rw [Subgroup.coe_mul, SubgroupClass.coe_zpow, SubgroupClass.coe_zpow, coe_torusGen₁,
      coe_torusGen₂, ← map_zpow, ← map_zpow, ← map_mul]
  rw [hval] at hc
  obtain ⟨h0, h1, h2⟩ := diagGL_eq_scalar hc
  have e0 : ζ ^ i = c := by simpa using h0
  have e1 : (ζ ^ i)⁻¹ * ζ ^ j = c := by simpa [inv_zpow] using h1
  have e2 : (ζ ^ j)⁻¹ = c := by simpa [inv_zpow] using h2
  have hb : ζ ^ j = ζ ^ i * ζ ^ i := by
    calc ζ ^ j = ζ ^ i * ((ζ ^ i)⁻¹ * ζ ^ j) := (mul_inv_cancel_left _ _).symm
      _ = ζ ^ i * c := by rw [e1]
      _ = ζ ^ i * ζ ^ i := by rw [e0]
  have hc' : ζ ^ j = (ζ ^ i)⁻¹ := inv_eq_iff_eq_inv.mp (e2.trans e0.symm)
  have e1' : ζ ^ (2 * i - j) = 1 := by
    rw [show (2 : ℤ) * i - j = i + i + -j by ring, zpow_add, zpow_add, zpow_neg, hb,
      mul_inv_cancel]
  have e2' : ζ ^ (i + j) = 1 := by
    rw [zpow_add, hc', mul_inv_cancel]
  have d1 : (9 : ℤ) ∣ 2 * i - j := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr e1'
    rw [hζ] at this
    exact_mod_cast this
  have d2 : (9 : ℤ) ∣ i + j := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr e2'
    rw [hζ] at this
    exact_mod_cast this
  omega

theorem swapMat_mul_diagonal {F : Type} [Field F] {d : Fin 3 → F} (hd : d 0 = d 1) :
    (swapMat : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal d =
      Matrix.diagonal d * swapMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, hd]

theorem swapGL_comm_diagGL {F : Type} [Field F] {y : Fin 3 → Fˣ} (hy : y 0 = y 1) :
    swapGL * diagGL y = diagGL y * swapGL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_swapGL, coe_diagGL]
  exact swapMat_mul_diagonal (d := fun k => (y k : F))
    (by show (y 0 : F) = (y 1 : F); rw [hy])

theorem swapEl_sq {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) : swapEl h ^ 2 = 1 := by
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, coe_swapEl, Subgroup.coe_one, sq]
  apply Units.ext
  rw [Units.val_mul, coe_swapGL, Units.val_one, swapMat_mul_self]

theorem swapEl_comm {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (ζ : Fˣ)
    (hζ : orderOf ζ = 9) :
    swapEl h * (torusGen₁ h ζ hζ * torusGen₂ h ζ hζ ^ 2) =
      (torusGen₁ h ζ hζ * torusGen₂ h ζ hζ ^ 2) * swapEl h := by
  have hy : (![ζ, ζ⁻¹, 1] * ![1, ζ, ζ⁻¹] ^ 2 : Fin 3 → Fˣ) 0 =
      (![ζ, ζ⁻¹, 1] * ![1, ζ, ζ⁻¹] ^ 2 : Fin 3 → Fˣ) 1 := by
    change ζ * (1 : Fˣ) ^ 2 = ζ⁻¹ * ζ ^ 2
    group
  apply Subtype.ext
  simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, coe_swapEl, coe_torusGen₁,
    coe_torusGen₂]
  rw [← map_pow, ← map_mul]
  exact swapGL_comm_diagGL hy

theorem swapEl_not_central {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) :
    swapEl h ∉ Subgroup.center (unitarySU 2 3 F 3) := by
  rw [center_unitarySU_three (h := h) (by norm_num), mem_unitaryScalars]
  rintro ⟨c, -, -, hc⟩
  have h01 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 1) hc
  simp [coe_swapEl, coe_swapGL, swapMat, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply] at h01

theorem rot_center_card {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) :
    Nat.card (Subgroup.center (unitarySU 2 3 F 3)) ≤ 3 := by
  rw [center_unitarySU_three (h := h) (by norm_num),
    card_unitaryScalars (n := 3) h (by norm_num)]
  norm_num

@[expose] noncomputable def rotDataOf {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (ζ : Fˣ) (hζ : orderOf ζ = 9) : RotData (unitarySU 2 3 F 3) where
  g₁ := torusGen₁ h ζ hζ
  g₂ := torusGen₂ h ζ hζ
  t := swapEl h
  g_comm := torusGen_comm h ζ hζ
  g_indep := fun i j hc => torusGen_indep h ζ hζ i j hc
  t_sq := swapEl_sq h
  t_not_central := swapEl_not_central h
  t_comm := swapEl_comm h ζ hζ
  center_card := rot_center_card h

theorem rotDataOf_field {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (ζ : Fˣ)
    (hζ : orderOf ζ = 9) (σ : F ≃+* F) :
    ∃ k : ℤ, suField h σ (torusGen₁ h ζ hζ) = torusGen₁ h ζ hζ ^ k ∧
      suField h σ (torusGen₂ h ζ hζ) = torusGen₂ h ζ hζ ^ k ∧
      suField h σ (swapEl h) = swapEl h := by
  have hprim : IsPrimitiveRoot (ζ : F) 9 :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζ)
  have hσ : σ (ζ : F) ^ 9 = 1 := by
    rw [← map_pow, hprim.pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hσ
  have hu : Units.map (σ : F →* F) ζ = ζ ^ i := by
    apply Units.ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hi.symm
  refine ⟨(i : ℤ), ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_suField, coe_torusGen₁, glAut_diagGL, SubgroupClass.coe_zpow, coe_torusGen₁,
      ← map_zpow]
    congr 1
    funext k
    fin_cases k <;> simp [hu, inv_zpow]
  · apply Subtype.ext
    rw [coe_suField, coe_torusGen₂, glAut_diagGL, SubgroupClass.coe_zpow, coe_torusGen₂,
      ← map_zpow]
    congr 1
    funext k
    fin_cases k <;> simp [hu, inv_zpow]
  · apply Subtype.ext
    rw [coe_suField, coe_swapEl, glAut_swapGL]

@[expose] noncomputable def rotDataSU {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) :
    RotData (unitarySU 2 3 F 3) :=
  rotDataOf h (Classical.choose (exists_orderOf_nine h))
    (Classical.choose_spec (exists_orderOf_nine h))

theorem rotDataSU_field {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (σ : F ≃+* F) :
    ∃ k : ℤ, suField h σ (rotDataSU h).g₁ = (rotDataSU h).g₁ ^ k ∧
      suField h σ (rotDataSU h).g₂ = (rotDataSU h).g₂ ^ k ∧
      suField h σ (rotDataSU h).t = (rotDataSU h).t :=
  rotDataOf_field h (Classical.choose (exists_orderOf_nine h))
    (Classical.choose_spec (exists_orderOf_nine h)) σ

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
