module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieTorus
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelL3

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3
  CFSG.Quasithin.H13.F431.L3.P3

abbrev Ln (F : Type) [Field F] [CharP F 2] : Subgroup (projectiveSL 3 F) :=
  Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))

abbrev Pt (F : Type) [Field F] [CharP F 2] : Subgroup (projectiveSL 3 F) :=
  Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))

@[expose] def uElt {F : Type} [Field F] (a b c : F) : projectiveSL 3 F :=
  xP a * yP b * wP (c - a * b)

theorem wP_xP_yP_comm {F : Type} [Field F] (c a b : F) :
    wP c * xP a * yP b = xP a * yP b * wP c := by
  rw [wP_mul_xP, mul_assoc, wP_mul_yP, mul_assoc]

theorem uElt_mem_U {F : Type} [Field F] [CharP F 2] (a b c : F) :
    uElt a b c ∈ projUnitriangular 3 F := by
  unfold uElt
  exact mem_Ubar.mpr ⟨c - a * b, a, b, (wP_xP_yP_comm _ _ _).symm⟩

theorem wP_xP_yP_eq_uElt {F : Type} [Field F] (a b c : F) :
    wP c * xP a * yP b = uElt a b (c + a * b) := by
  unfold uElt
  rw [add_sub_cancel_right, wP_xP_yP_comm]

theorem coe_wxy {F : Type} [Field F] (c a b : F) :
    ((wMat c * xMat a * yMat b : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, a, c + a * b; 0, 1, b; 0, 0, 1] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, xMat, yMat, wM, xM, yM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem B0_eq_normalizer {F : Type} [Field F] [Finite F] [CharP F 2] :
    Ln F ⊓ Pt F = Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := by
  rw [inf_comm]
  exact CFSG.QuasithinUnique.Borel252.BorelData.inf_norm
    (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := F))

theorem torus_mem_B0 {F : Type} [Field F] [Finite F] [CharP F 2] {g : projectiveSL 3 F}
    (hg : g ∈ torus3 F) : g ∈ Ln F ⊓ Pt F := by
  rw [B0_eq_normalizer]
  exact torus3_le_normalizer hg

theorem uElt_mem_B0 {F : Type} [Field F] [Finite F] [CharP F 2] (a b c : F) :
    uElt a b c ∈ Ln F ⊓ Pt F := by
  rw [B0_eq_normalizer]
  exact Subgroup.le_normalizer (uElt_mem_U a b c)

theorem torus_inf_U_eq_one {F : Type} [Field F] [CharP F 2] {g : projectiveSL 3 F}
    (hT : g ∈ torus3 F) (hU : g ∈ projUnitriangular 3 F) : g = 1 := by
  obtain ⟨t1, t2, rfl⟩ := mem_torus3.mp hT
  obtain ⟨c, a, b, hg⟩ := mem_Ubar.mp hU
  have hM : proj 3 F (dMat t1 t2) = proj 3 F (wMat c * xMat a * yMat b) := by
    rw [hg]
    simp only [wP, xP, yP, map_mul]
  obtain ⟨r, -, hr⟩ := mem_scalars.mp (proj_eq_proj_iff.mp hM)
  have hMM : ((wMat c * xMat a * yMat b : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      (dMat t1 t2 : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (r : F) := by
    rw [← hr, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have e01 := congrFun (congrFun hMM 0) 1
  have e12 := congrFun (congrFun hMM 1) 2
  have e02 := congrFun (congrFun hMM 0) 2
  rw [coe_wxy, coe_dMat] at e01 e12 e02
  simp [Matrix.mul_diagonal, Matrix.scalar_apply, Matrix.diagonal_apply] at e01 e12 e02
  have ha : a = 0 := e01
  have hb : b = 0 := e12
  have hc : c = 0 := by simpa [ha, hb] using e02
  rw [hg, ha, hb, hc, (wP_eq_one_iff 0).mpr rfl, (xP_eq_one_iff 0).mpr rfl,
    (yP_eq_one_iff 0).mpr rfl, mul_one, one_mul]

theorem uElt_mul_torus_inj {F : Type} [Field F] [CharP F 2] [Finite F] {a b c a' b' c' : F}
    {τ τ' : ↥(torus3 F)}
    (h : uElt a b c * (τ : projectiveSL 3 F) = uElt a' b' c' * (τ' : projectiveSL 3 F)) :
    a = a' ∧ b = b' ∧ c = c' ∧ τ = τ' := by
  have hcomm : (uElt a' b' c')⁻¹ * uElt a b c =
      (τ' : projectiveSL 3 F) * (τ : projectiveSL 3 F)⁻¹ := by
    calc (uElt a' b' c')⁻¹ * uElt a b c
        = (uElt a' b' c')⁻¹ * (uElt a b c * (τ : projectiveSL 3 F)) *
            (τ : projectiveSL 3 F)⁻¹ := by group
      _ = (uElt a' b' c')⁻¹ * (uElt a' b' c' * (τ' : projectiveSL 3 F)) *
            (τ : projectiveSL 3 F)⁻¹ := by rw [h]
      _ = (τ' : projectiveSL 3 F) * (τ : projectiveSL 3 F)⁻¹ := by group
  have hU : (uElt a' b' c')⁻¹ * uElt a b c ∈ projUnitriangular 3 F :=
    mul_mem (inv_mem (uElt_mem_U a' b' c')) (uElt_mem_U a b c)
  have hT : (τ' : projectiveSL 3 F) * (τ : projectiveSL 3 F)⁻¹ ∈ torus3 F :=
    mul_mem τ'.2 (inv_mem τ.2)
  have h1 : (τ' : projectiveSL 3 F) * (τ : projectiveSL 3 F)⁻¹ = 1 :=
    torus_inf_U_eq_one hT (by rw [← hcomm]; exact hU)
  have hττ : τ' = τ := Subtype.ext (mul_inv_eq_one.mp h1)
  have hu : uElt a' b' c' = uElt a b c := by
    apply inv_mul_eq_one.mp
    rw [hcomm, h1]
  unfold uElt at hu
  rw [← wP_xP_yP_comm, ← wP_xP_yP_comm] at hu
  obtain ⟨hc', ha, hb⟩ := U_ext hu
  refine ⟨ha.symm, hb.symm, ?_, hττ.symm⟩
  have hab : a * b = a' * b' := by rw [ha, hb]
  linear_combination hab - hc'

@[expose] def nuFrob {F : Type} [Field F] (ε : Bool) (x : F) : F :=
  if ε then x ^ 2 else x

@[expose] noncomputable def nuFrobEquiv (F : Type) [Field F] [Finite F] [CharP F 2] : F ≃+* F :=
  RingEquiv.ofBijective (frobenius F 2)
    ⟨frobenius_inj F 2, Finite.injective_iff_surjective.mp (frobenius_inj F 2)⟩

theorem nuFrobEquiv_apply {F : Type} [Field F] [Finite F] [CharP F 2] (x : F) :
    nuFrobEquiv F x = x ^ 2 := rfl

@[expose] noncomputable def nuFrobEq (F : Type) [Field F] [Finite F] [CharP F 2] (ε : Bool) :
    F ≃+* F :=
  if ε then nuFrobEquiv F else RingEquiv.refl F

theorem nuFrobEq_apply {F : Type} [Field F] [Finite F] [CharP F 2] (ε : Bool) (x : F) :
    nuFrobEq F ε x = nuFrob ε x := by
  cases ε
  · rfl
  · rfl

theorem nuFrob_sub_mul {F : Type} [Field F] [CharP F 2] (ε : Bool) (a b c : F) :
    nuFrob ε (c - a * b) = nuFrob ε c - nuFrob ε a * nuFrob ε b := by
  cases ε
  · rfl
  · simp only [nuFrob, if_true]
    linear_combination (-(a * b * (c - a * b))) * (CharTwo.two_eq_zero : (2 : F) = 0)

@[expose] def nuDiagGL {F : Type} [Field F] (s t : Fˣ) : GL (Fin 3) F :=
  Units.mk (Matrix.diagonal ![(s : F) * (t : F), (t : F), 1])
    (Matrix.diagonal ![((s : F) * (t : F))⁻¹, (t : F)⁻¹, 1])
    (by
      have hs : (s : F) ≠ 0 := Units.ne_zero s
      have ht : (t : F) ≠ 0 := Units.ne_zero t
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp <;> field_simp)
    (by
      have hs : (s : F) ≠ 0 := Units.ne_zero s
      have ht : (t : F) ≠ 0 := Units.ne_zero t
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp <;> field_simp)

theorem coe_nuDiagGL {F : Type} [Field F] (s t : Fˣ) :
    ((nuDiagGL (F := F) s t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(s : F) * (t : F), (t : F), 1] :=
  rfl

theorem coe_nuDiagGL_inv {F : Type} [Field F] (s t : Fˣ) :
    (((nuDiagGL (F := F) s t)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![((s : F) * (t : F))⁻¹, (t : F)⁻¹, 1] :=
  rfl

theorem conjAut_nuDiag_xP {F : Type} [Field F] (s t : Fˣ) (a : F) :
    conjAut 3 F (nuDiagGL s t) (xP a) = xP ((s : F) * a) := by
  have hs : (s : F) ≠ 0 := Units.ne_zero s
  have ht : (t : F) ≠ 0 := Units.ne_zero t
  unfold xP
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_nuDiagGL, coe_nuDiagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMat, xM, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem conjAut_nuDiag_yP {F : Type} [Field F] (s t : Fˣ) (b : F) :
    conjAut 3 F (nuDiagGL s t) (yP b) = yP ((t : F) * b) := by
  have hs : (s : F) ≠ 0 := Units.ne_zero s
  have ht : (t : F) ≠ 0 := Units.ne_zero t
  unfold yP
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_nuDiagGL, coe_nuDiagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yMat, yM, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem conjAut_nuDiag_wP {F : Type} [Field F] (s t : Fˣ) (c : F) :
    conjAut 3 F (nuDiagGL s t) (wP c) = wP ((s : F) * (t : F) * c) := by
  have hs : (s : F) ≠ 0 := Units.ne_zero s
  have ht : (t : F) ≠ 0 := Units.ne_zero t
  unfold wP
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_nuDiagGL, coe_nuDiagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, wM, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem conjAut_nuDiag_dMat {F : Type} [Field F] (s t t1 t2 : Fˣ) :
    conjAut 3 F (nuDiagGL s t) (proj 3 F (dMat t1 t2)) = proj 3 F (dMat t1 t2) := by
  have hs : (s : F) ≠ 0 := Units.ne_zero s
  have ht : (t : F) ≠ 0 := Units.ne_zero t
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_nuDiagGL, coe_nuDiagGL_inv, coe_dMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> field_simp

theorem coe_sl_map_apply {F : Type} [Field F] (σ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    ((Matrix.SpecialLinearGroup.map σ.toRingHom g : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) i j = σ ((g : Matrix (Fin 3) (Fin 3) F) i j) :=
  rfl

theorem fieldAut_xP {F : Type} [Field F] (σ : F ≃+* F) (a : F) :
    fieldAut 3 F σ (xP a) = xP (σ a) := by
  unfold xP
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rw [coe_sl_map_apply] <;> simp [xMat, xM]

theorem fieldAut_yP {F : Type} [Field F] (σ : F ≃+* F) (b : F) :
    fieldAut 3 F σ (yP b) = yP (σ b) := by
  unfold yP
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rw [coe_sl_map_apply] <;> simp [yMat, yM]

theorem fieldAut_wP {F : Type} [Field F] (σ : F ≃+* F) (c : F) :
    fieldAut 3 F σ (wP c) = wP (σ c) := by
  unfold wP
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rw [coe_sl_map_apply] <;> simp [wMat, wM]

theorem cube_units {F : Type} [Field F] (hq : Nat.card F = 4) (t : Fˣ) : (t : F) ^ 3 = 1 :=
  LinearFieldFour.pow_three_eq_one hq t.ne_zero

theorem sq_units_eq_inv {F : Type} [Field F] (hq : Nat.card F = 4) (t : Fˣ) : t ^ 2 = t⁻¹ := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  have h := cube_units hq t
  have ht : (t : F) ≠ 0 := t.ne_zero
  field_simp
  linear_combination h

theorem fieldAut_nuFrob_dMat {F : Type} [Field F] [Finite F] [CharP F 2] (t1 t2 : Fˣ) :
    fieldAut 3 F (nuFrobEquiv F) (proj 3 F (dMat t1 t2)) = proj 3 F (dMat (t1 ^ 2) (t2 ^ 2)) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dMat, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      nuFrobEquiv_apply, Units.val_pow_eq_pow_val, mul_pow, inv_pow, mul_inv]

theorem fieldAut_refl_proj {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    fieldAut 3 F (RingEquiv.refl F) (proj 3 F g) = proj 3 F g := by
  rw [fieldAut_proj]
  congr 1

@[expose] noncomputable def nuTheta (F : Type) [Field F] [Finite F] [CharP F 2] (s t : Fˣ)
    (ε : Bool) : MulAut (projectiveSL 3 F) :=
  conjAut 3 F (nuDiagGL s t) * fieldAut 3 F (nuFrobEq F ε)

theorem nuTheta_xP {F : Type} [Field F] [Finite F] [CharP F 2] (s t : Fˣ) (ε : Bool) (a : F) :
    nuTheta F s t ε (xP a) = xP ((s : F) * nuFrob ε a) := by
  rw [nuTheta, MulAut.mul_apply, fieldAut_xP, nuFrobEq_apply, conjAut_nuDiag_xP]

theorem nuTheta_yP {F : Type} [Field F] [Finite F] [CharP F 2] (s t : Fˣ) (ε : Bool) (b : F) :
    nuTheta F s t ε (yP b) = yP ((t : F) * nuFrob ε b) := by
  rw [nuTheta, MulAut.mul_apply, fieldAut_yP, nuFrobEq_apply, conjAut_nuDiag_yP]

theorem nuTheta_wP {F : Type} [Field F] [Finite F] [CharP F 2] (s t : Fˣ) (ε : Bool) (c : F) :
    nuTheta F s t ε (wP c) = wP ((s : F) * (t : F) * nuFrob ε c) := by
  rw [nuTheta, MulAut.mul_apply, fieldAut_wP, nuFrobEq_apply, conjAut_nuDiag_wP]

theorem nuTheta_uElt {F : Type} [Field F] [Finite F] [CharP F 2] (s t : Fˣ) (ε : Bool)
    (a b c : F) :
    nuTheta F s t ε (uElt a b c) =
      uElt ((s : F) * nuFrob ε a) ((t : F) * nuFrob ε b) ((s : F) * (t : F) * nuFrob ε c) := by
  unfold uElt
  rw [map_mul, map_mul, nuTheta_xP, nuTheta_yP, nuTheta_wP, nuFrob_sub_mul]
  congr 2
  ring

theorem nuTheta_torus_false {F : Type} [Field F] [Finite F] [CharP F 2] (s t t1 t2 : Fˣ) :
    nuTheta F s t false (proj 3 F (dMat t1 t2)) = proj 3 F (dMat t1 t2) := by
  rw [nuTheta, MulAut.mul_apply]
  have h : nuFrobEq F false = RingEquiv.refl F := rfl
  rw [h, fieldAut_refl_proj, conjAut_nuDiag_dMat]

theorem nuTheta_torus_true {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4)
    (s t t1 t2 : Fˣ) :
    nuTheta F s t true (proj 3 F (dMat t1 t2)) = (proj 3 F (dMat t1 t2))⁻¹ := by
  rw [nuTheta, MulAut.mul_apply]
  have h : nuFrobEq F true = nuFrobEquiv F := rfl
  rw [h, fieldAut_nuFrob_dMat, conjAut_nuDiag_dMat, ← map_inv, dMat_inv, sq_units_eq_inv hq t1,
    sq_units_eq_inv hq t2]

theorem nuTheta_torus {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4)
    (s t : Fˣ) (ε : Bool) (τ : ↥(torus3 F)) :
    nuTheta F s t ε (τ : projectiveSL 3 F) =
      ((if ε then τ⁻¹ else τ : ↥(torus3 F)) : projectiveSL 3 F) := by
  obtain ⟨t1, t2, hτ⟩ := mem_torus3.mp τ.2
  cases ε
  · simp only [Bool.false_eq_true, if_false]
    rw [hτ, nuTheta_torus_false]
  · simp only [if_true]
    rw [Subgroup.coe_inv, hτ, nuTheta_torus_true hq]

theorem nuTheta_uElt_mul {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4)
    (s t : Fˣ) (ε : Bool) (a b c : F) (τ : ↥(torus3 F)) :
    nuTheta F s t ε (uElt a b c * (τ : projectiveSL 3 F)) =
      uElt ((s : F) * nuFrob ε a) ((t : F) * nuFrob ε b) ((s : F) * (t : F) * nuFrob ε c) *
        ((if ε then τ⁻¹ else τ : ↥(torus3 F)) : projectiveSL 3 F) := by
  rw [map_mul, nuTheta_uElt, nuTheta_torus hq]

@[expose] def nuNF {F : Type} [Field F] [Finite F] [CharP F 2] (x : F × F × F × ↥(torus3 F)) :
    ↥(Ln F ⊓ Pt F) :=
  ⟨uElt x.1 x.2.1 x.2.2.1 * (x.2.2.2 : projectiveSL 3 F),
    Subgroup.mul_mem _ (uElt_mem_B0 _ _ _) (torus_mem_B0 x.2.2.2.2)⟩

theorem nuNF_injective {F : Type} [Field F] [Finite F] [CharP F 2] :
    Function.Injective (nuNF (F := F)) := by
  rintro ⟨a, b, c, τ⟩ ⟨a', b', c', τ'⟩ h
  have h' : uElt a b c * (τ : projectiveSL 3 F) = uElt a' b' c' * (τ' : projectiveSL 3 F) :=
    congrArg Subtype.val h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := uElt_mul_torus_inj h'
  rfl

theorem nuNF_surjective {F : Type} [Field F] [Finite F] [CharP F 2] :
    Function.Surjective (nuNF (F := F)) := by
  rintro ⟨g, hg⟩
  rw [B0_eq_normalizer] at hg
  obtain ⟨u, hu, τ, hτ, rfl⟩ := torus3_mul hg
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hu
  refine ⟨(a, b, c + a * b, ⟨τ, hτ⟩), Subtype.ext ?_⟩
  change uElt a b (c + a * b) * (τ : projectiveSL 3 F) =
    wP c * xP a * yP b * (τ : projectiveSL 3 F)
  rw [wP_xP_yP_eq_uElt]

@[expose] noncomputable def nuNFEquiv (F : Type) [Field F] [Finite F] [CharP F 2] :
    (F × F × F × ↥(torus3 F)) ≃ ↥(Ln F ⊓ Pt F) :=
  Equiv.ofBijective (nuNF (F := F)) ⟨nuNF_injective, nuNF_surjective⟩

theorem nuNFEquiv_val {F : Type} [Field F] [Finite F] [CharP F 2] (x : F × F × F × ↥(torus3 F)) :
    ((nuNFEquiv F x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
      uElt x.1 x.2.1 x.2.2.1 * (x.2.2.2 : projectiveSL 3 F) :=
  rfl

@[expose] def nuCoord {F : Type} [Field F] (s t : Fˣ) (κ₁ κ₂ : F) (ε : Bool)
    (x : F × F × F × ↥(torus3 F)) : F × F × F × ↥(torus3 F) :=
  ((s : F) * nuFrob ε x.1, (t : F) * nuFrob ε x.2.1,
    (s : F) * (t : F) * nuFrob ε x.2.2.1 + κ₁ * nuFrob ε x.1 ^ 2 + κ₂ * nuFrob ε x.2.1 ^ 2,
    if ε then x.2.2.2⁻¹ else x.2.2.2)

@[expose] noncomputable def nuMap {F : Type} [Field F] [Finite F] [CharP F 2] (s t : Fˣ)
    (κ₁ κ₂ : F) (ε : Bool) (b : ↥(Ln F ⊓ Pt F)) : ↥(Ln F ⊓ Pt F) :=
  nuNFEquiv F (nuCoord s t κ₁ κ₂ ε ((nuNFEquiv F).symm b))

theorem nuMap_nuNFEquiv {F : Type} [Field F] [Finite F] [CharP F 2] (s t : Fˣ) (κ₁ κ₂ : F)
    (ε : Bool) (x : F × F × F × ↥(torus3 F)) :
    nuMap s t κ₁ κ₂ ε (nuNFEquiv F x) = nuNFEquiv F (nuCoord s t κ₁ κ₂ ε x) := by
  simp [nuMap]

theorem mem_iff_of_map_le {G : Type} [Group G] [Finite G] (θ : MulAut G) (S : Subgroup G)
    (h : ∀ x ∈ S, θ x ∈ S) (x : G) : x ∈ S ↔ θ x ∈ S := by
  have hmap : S.map θ.toMonoidHom = S := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    · rw [Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
  constructor
  · exact h x
  · intro hx
    have hmem : θ x ∈ S.map θ.toMonoidHom := by
      rw [hmap]
      exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    have hyx' : y = x := θ.injective hyx
    exact hyx' ▸ hy

theorem mem_normalizer_iff_of_aut {G : Type} [Group G] (θ : MulAut G) (S : Subgroup G)
    (hS : ∀ x, x ∈ S ↔ θ x ∈ S) (x : G) :
    x ∈ Subgroup.normalizer (S : Set G) ↔ θ x ∈ Subgroup.normalizer (S : Set G) := by
  simp only [Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    obtain ⟨k, rfl⟩ := θ.surjective y
    rw [show θ x * θ k * (θ x)⁻¹ = θ (x * k * x⁻¹) by simp [map_mul, map_inv]]
    exact (hS k).symm.trans ((hx k).trans (hS _))
  · intro hθ k
    have h1 := hθ (θ k)
    rw [show θ x * θ k * (θ x)⁻¹ = θ (x * k * x⁻¹) by simp [map_mul, map_inv]] at h1
    exact (hS k).trans (h1.trans (hS _).symm)

@[expose] def nuRestrict {G : Type} [Group G] (θ : MulAut G) (K : Subgroup G)
    (hK : ∀ x, x ∈ K ↔ θ x ∈ K) : MulAut K where
  toFun x := ⟨θ x, (hK (x : G)).mp x.2⟩
  invFun y :=
    ⟨θ.symm y, (hK (θ.symm (y : G))).mpr (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (θ.symm_apply_apply x)
  right_inv y := Subtype.ext (θ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul θ (x : G) (y : G))

theorem leaf_T13 {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4) (s t : Fˣ)
    (ε : Bool) :
    ∃ a : MulAut ↥(Ln F),
      (∀ m : ↥(Ln F), (m : projectiveSL 3 F) ∈ Pt F ↔
        ((a m : ↥(Ln F)) : projectiveSL 3 F) ∈ Pt F) ∧
      ∀ (b : ↥(Ln F ⊓ Pt F)) (m : ↥(Ln F)), (m : projectiveSL 3 F) = (b : projectiveSL 3 F) →
        ((a m : ↥(Ln F)) : projectiveSL 3 F) =
          ((nuMap s t 0 0 ε b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) := by
  have hV2 : ∀ x ∈ (V2 : Subgroup (projectiveSL 3 F)),
      nuTheta F s t ε x ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
    intro x hx
    obtain ⟨b, c, rfl⟩ := mem_V2.mp hx
    rw [map_mul, nuTheta_yP, nuTheta_wP]
    exact mem_V2.mpr ⟨_, _, rfl⟩
  have hV1 : ∀ x ∈ (V1 : Subgroup (projectiveSL 3 F)),
      nuTheta F s t ε x ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
    intro x hx
    obtain ⟨a, c, rfl⟩ := mem_V1.mp hx
    rw [map_mul, nuTheta_xP, nuTheta_wP]
    exact mem_V1.mpr ⟨_, _, rfl⟩
  have hLn : ∀ x, x ∈ Ln F ↔ nuTheta F s t ε x ∈ Ln F :=
    mem_normalizer_iff_of_aut (nuTheta F s t ε) _ (mem_iff_of_map_le _ _ hV2)
  have hPt : ∀ x, x ∈ Pt F ↔ nuTheta F s t ε x ∈ Pt F :=
    mem_normalizer_iff_of_aut (nuTheta F s t ε) _ (mem_iff_of_map_le _ _ hV1)
  refine ⟨nuRestrict (nuTheta F s t ε) (Ln F) hLn, fun m => hPt m, ?_⟩
  intro b m hmb
  change nuTheta F s t ε (m : projectiveSL 3 F) = _
  rw [hmb]
  obtain ⟨x, rfl⟩ := (nuNFEquiv F).surjective b
  rw [nuMap_nuNFEquiv, nuNFEquiv_val, nuNFEquiv_val]
  obtain ⟨a, b', c, τ⟩ := x
  simp only [nuCoord, zero_mul, add_zero]
  exact nuTheta_uElt_mul hq s t ε a b' c τ

end CFSG.GH74.QTGen4.DSGen4.L34
