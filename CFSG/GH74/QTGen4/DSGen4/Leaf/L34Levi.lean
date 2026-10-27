module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieV1
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieV2
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover CFSG.QuasithinUnique.Setup.X7a

theorem cube_eq_one_of_card_four {F : Type} [Field F] [Finite F] (hq : Nat.card F = 4) {x : F}
    (hx : x ≠ 0) : x ^ 3 = 1 := by
  haveI := Fintype.ofFinite F
  have hc : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hq
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rw [hc] at h
  simpa using h

theorem mem_pCore_iff_mem_pCoreOf {G : Type*} [Group G] (N : Subgroup G) (x : ↥N) :
    x ∈ CFSG.pCore 2 N ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 N := by
  unfold CFSG.Open.pCoreOf
  constructor
  · intro hx
    exact Subgroup.mem_map_of_mem _ hx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hxy : y = x := Subtype.ext hyx
    exact hxy ▸ hy

@[expose] noncomputable def liftOfComp {Q N S : Type*} [Group Q] [Group N] [Group S] (q : Q →* N)
    (hq : Function.Surjective q) (ψ : Q →* S) (hψ : q.ker ≤ ψ.ker) : N →* S :=
  (QuotientGroup.lift q.ker ψ hψ).comp
    (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.toMonoidHom

theorem liftOfComp_apply {Q N S : Type*} [Group Q] [Group N] [Group S] (q : Q →* N)
    (hq : Function.Surjective q) (ψ : Q →* S) (hψ : q.ker ≤ ψ.ker) (g : Q) :
    liftOfComp q hq ψ hψ (q g) = ψ g := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q g) = (g : Q ⧸ q.ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  show QuotientGroup.lift q.ker ψ hψ
    ((QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q g)) = ψ g
  rw [h]
  rfl

section Roots

variable {F : Type} [Field F]

theorem coe_yMat_mul_wMat (b c : F) :
    ((yMat b * wMat c : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, c; 0, 1, b; 0, 0, 1] := by
  show yM b * wM c = !![1, 0, c; 0, 1, b; 0, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yM, wM, Matrix.mul_apply, Fin.sum_univ_three]

theorem coe_xMat_mul_wMat (a c : F) :
    ((xMat a * wMat c : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, a, c; 0, 1, 0; 0, 0, 1] := by
  show xM a * wM c = !![1, a, c; 0, 1, 0; 0, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xM, wM, Matrix.mul_apply, Fin.sum_univ_three]

end Roots

section LineBlock

variable {F : Type} [Field F] [CharP F 2]

@[expose] def tlBlock (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

@[expose] def levMat (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  (tlBlock M).det • tlBlock M

theorem det_eq_tlBlock (G : Matrix (Fin 3) (Fin 3) F) (h20 : G 2 0 = 0) (h21 : G 2 1 = 0) :
    G.det = (tlBlock G).det * G 2 2 := by
  simp [tlBlock, Matrix.det_fin_two, Matrix.det_fin_three, h20, h21] <;> ring

theorem tlBlock_mul {G H : Matrix (Fin 3) (Fin 3) F} (h20 : H 2 0 = 0) (h21 : H 2 1 = 0) :
    tlBlock (G * H) = tlBlock G * tlBlock H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tlBlock, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, h20, h21]

theorem levMat_mul {G H : Matrix (Fin 3) (Fin 3) F} (h20 : H 2 0 = 0) (h21 : H 2 1 = 0) :
    levMat (G * H) = levMat G * levMat H := by
  unfold levMat
  rw [tlBlock_mul h20 h21, Matrix.det_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem levMat_one : levMat (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat, tlBlock, Matrix.det_fin_two]

theorem det_levMat {G : Matrix (Fin 3) (Fin 3) F} (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1)
    (hG : G.det = 1) (h20 : G 2 0 = 0) (h21 : G 2 1 = 0) : (levMat G).det = 1 := by
  have hb := det_eq_tlBlock G h20 h21
  have hA : (tlBlock G).det ≠ 0 := by
    intro h0
    rw [hb, h0, zero_mul] at hG
    exact zero_ne_one hG
  unfold levMat
  rw [Matrix.det_smul, Fintype.card_fin]
  linear_combination hq3 _ hA

@[expose] noncomputable def levHom (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1) :
    ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 1) →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨levMat (g.1 : Matrix (Fin 3) (Fin 3) F), det_levMat hq3 g.1.2
    (CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff.mp g.2).1
    (CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff.mp g.2).2⟩
  map_one' := Subtype.ext levMat_one
  map_mul' g h := Subtype.ext (levMat_mul (CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff.mp h.2).1
    (CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff.mp h.2).2)

theorem levMat_scalar {c : F} (hc : c ^ 3 = 1) : levMat (Matrix.scalar (Fin 3) c) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [levMat, tlBlock, Matrix.det_fin_two, Matrix.scalar_apply, Matrix.diagonal_apply] <;>
    linear_combination hc

theorem levHom_eq_one_of_scalar (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1)
    {g : ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 1)}
    (hg : ((g : Matrix.SpecialLinearGroup (Fin 3) F)) ∈ scalars 3 F) : levHom hq3 g = 1 := by
  obtain ⟨c, hc, hgc⟩ := mem_scalars.mp hg
  apply Subtype.ext
  show levMat ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
  rw [hgc]
  apply levMat_scalar
  rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]

theorem levHom_eq_one_of_block (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1)
    {g : ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 1)}
    (hb : tlBlock ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1) :
    levHom hq3 g = 1 := by
  apply Subtype.ext
  show levMat ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
  unfold levMat
  rw [hb, Matrix.det_one, one_smul]

theorem levHom_surjective (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1) :
    Function.Surjective (levHom hq3) := by
  intro B
  have hB := B.2
  rw [Matrix.det_fin_two] at hB
  let M : Matrix (Fin 3) (Fin 3) F :=
    !![(B : Matrix (Fin 2) (Fin 2) F) 0 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
      (B : Matrix (Fin 2) (Fin 2) F) 1 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, 0, 1]
  have hdet : M.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [M]
    linear_combination hB
  let Mg : Matrix.SpecialLinearGroup (Fin 3) F := ⟨M, hdet⟩
  have hMg : Mg ∈ CFSG.QuasithinUnique.Setup.X7a.Q3 F 1 :=
    CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff.mpr ⟨by simp [Mg, M], by simp [Mg, M]⟩
  refine ⟨⟨Mg, hMg⟩, Subtype.ext ?_⟩
  show levMat M = (B : Matrix (Fin 2) (Fin 2) F)
  have hT : tlBlock M = (B : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tlBlock, M]
  unfold levMat
  rw [hT, B.2, one_smul]

theorem levHom_eq_one_iff_V2 (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1)
    (g : ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 1)) :
    levHom hq3 g = 1 ↔
      proj 3 F (g : Matrix.SpecialLinearGroup (Fin 3) F) ∈
        CFSG.QuasithinUnique.Fin257.L3.V2 := by
  constructor
  · intro h
    obtain ⟨G, hGd⟩ : ∃ G : Matrix (Fin 3) (Fin 3) F,
        G = ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
    have hL : levMat G = 1 := by rw [hGd]; exact congrArg Subtype.val h
    have hGdet : G.det = 1 := by rw [hGd]; exact (g : Matrix.SpecialLinearGroup (Fin 3) F).2
    obtain ⟨h20, h21⟩ : G 2 0 = 0 ∧ G 2 1 = 0 := by
      rw [hGd]; exact CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff.mp g.2
    have hb : G.det = (tlBlock G).det * G 2 2 := det_eq_tlBlock G h20 h21
    have hδd : (tlBlock G).det * G 2 2 = 1 := by rw [← hb, hGdet]
    have hδ0 : (tlBlock G).det ≠ 0 := left_ne_zero_of_mul_eq_one hδd
    have hd0 : G 2 2 ≠ 0 := right_ne_zero_of_mul_eq_one hδd
    have hLA : (tlBlock G).det • tlBlock G = 1 := hL
    have e00 : (tlBlock G).det * G 0 0 = 1 := by
      have h' := congrFun (congrFun hLA 0) 0
      simpa [tlBlock] using h'
    have e11 : (tlBlock G).det * G 1 1 = 1 := by
      have h' := congrFun (congrFun hLA 1) 1
      simpa [tlBlock] using h'
    have e01 : (tlBlock G).det * G 0 1 = 0 := by
      have h' := congrFun (congrFun hLA 0) 1
      simpa [tlBlock] using h'
    have e10 : (tlBlock G).det * G 1 0 = 0 := by
      have h' := congrFun (congrFun hLA 1) 0
      simpa [tlBlock] using h'
    have f00 : G 0 0 = G 2 2 := by linear_combination (G 2 2) * e00 - (G 0 0) * hδd
    have f11 : G 1 1 = G 2 2 := by linear_combination (G 2 2) * e11 - (G 1 1) * hδd
    have f01 : G 0 1 = 0 := (mul_eq_zero.mp e01).resolve_left hδ0
    have f10 : G 1 0 = 0 := (mul_eq_zero.mp e10).resolve_left hδ0
    have he0 : (G 2 2)⁻¹ ≠ 0 := inv_ne_zero hd0
    have he3 : ((G 2 2)⁻¹) ^ 3 = 1 := hq3 _ he0
    let eu : Fˣ := Units.mk0 ((G 2 2)⁻¹) he0
    have heu : eu ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact he3
    let lam : Matrix.SpecialLinearGroup (Fin 3) F := scalarElement eu heu
    have hlam : lam ∈ scalars 3 F := scalarElement_mem_scalars eu heu
    have hlamval : (lam : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) ((G 2 2)⁻¹) :=
      coe_scalarElement eu heu
    have hu : lam * (g : Matrix.SpecialLinearGroup (Fin 3) F) =
        yMat ((G 2 2)⁻¹ * G 1 2) * wMat ((G 2 2)⁻¹ * G 0 2) := by
      apply Subtype.ext
      rw [coe_yMat_mul_wMat, Matrix.SpecialLinearGroup.coe_mul, hlamval, ← hGd]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, Matrix.diagonal_mul, f00, f11, f01, f10, h20, h21,
          inv_mul_cancel₀ hd0]
    have hpu : proj 3 F (lam * (g : Matrix.SpecialLinearGroup (Fin 3) F)) =
        proj 3 F (g : Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [map_mul, proj_eq_one_iff.mpr hlam, one_mul]
    rw [CFSG.QuasithinUnique.Fin257.L3.mem_V2]
    refine ⟨(G 2 2)⁻¹ * G 1 2, (G 2 2)⁻¹ * G 0 2, ?_⟩
    rw [yP, wP, ← map_mul, ← hu, hpu]
  · intro hV
    obtain ⟨b, c, hbc⟩ := (CFSG.QuasithinUnique.Fin257.L3.mem_V2).mp hV
    have hpu : proj 3 F (yMat b * wMat c) = proj 3 F (g : Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [map_mul]
      exact hbc.symm
    have hu0Q : yMat b * wMat c ∈ CFSG.QuasithinUnique.Setup.X7a.Q3 F 1 :=
      CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff.mpr
        ⟨by rw [coe_yMat_mul_wMat]; simp, by rw [coe_yMat_mul_wMat]; simp⟩
    have hsc : (yMat b * wMat c)⁻¹ * (g : Matrix.SpecialLinearGroup (Fin 3) F) ∈ scalars 3 F :=
      proj_eq_proj_iff.mp hpu
    have hlamQ : (yMat b * wMat c)⁻¹ * (g : Matrix.SpecialLinearGroup (Fin 3) F) ∈
        CFSG.QuasithinUnique.Setup.X7a.Q3 F 1 :=
      (CFSG.QuasithinUnique.Setup.X7a.Q3 F 1).mul_mem ((CFSG.QuasithinUnique.Setup.X7a.Q3 F 1).inv_mem hu0Q) g.2
    have hgsplit : g = ⟨yMat b * wMat c, hu0Q⟩ *
        ⟨(yMat b * wMat c)⁻¹ * (g : Matrix.SpecialLinearGroup (Fin 3) F), hlamQ⟩ :=
      Subtype.ext (mul_inv_cancel_left _ _).symm
    have hb1 : tlBlock ((yMat b * wMat c : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [coe_yMat_mul_wMat]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [tlBlock]
    calc levHom hq3 g
        = levHom hq3 (⟨yMat b * wMat c, hu0Q⟩ *
            ⟨(yMat b * wMat c)⁻¹ * (g : Matrix.SpecialLinearGroup (Fin 3) F), hlamQ⟩) :=
          congrArg (levHom hq3) hgsplit
      _ = 1 := by
          rw [map_mul, levHom_eq_one_of_block (g := ⟨yMat b * wMat c, hu0Q⟩) hq3 hb1,
            levHom_eq_one_of_scalar (g := ⟨_, hlamQ⟩) hq3 hsc, mul_one]

end LineBlock

section PointBlock

variable {F : Type} [Field F] [CharP F 2]

@[expose] def brBlock (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![M 1 1, M 1 2; M 2 1, M 2 2]

@[expose] def levMatR (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  (brBlock M).det • brBlock M

theorem det_eq_brBlock (G : Matrix (Fin 3) (Fin 3) F) (h10 : G 1 0 = 0) (h20 : G 2 0 = 0) :
    G.det = G 0 0 * (brBlock G).det := by
  simp [brBlock, Matrix.det_fin_two, Matrix.det_fin_three, h10, h20] <;> ring

theorem brBlock_mul {G H : Matrix (Fin 3) (Fin 3) F} (h10 : G 1 0 = 0) (h20 : G 2 0 = 0) :
    brBlock (G * H) = brBlock G * brBlock H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [brBlock, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, h10, h20]

theorem levMatR_mul {G H : Matrix (Fin 3) (Fin 3) F} (h10 : G 1 0 = 0) (h20 : G 2 0 = 0) :
    levMatR (G * H) = levMatR G * levMatR H := by
  unfold levMatR
  rw [brBlock_mul h10 h20, Matrix.det_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem levMatR_one : levMatR (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMatR, brBlock, Matrix.det_fin_two]

theorem det_levMatR {G : Matrix (Fin 3) (Fin 3) F} (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1)
    (hG : G.det = 1) (h10 : G 1 0 = 0) (h20 : G 2 0 = 0) : (levMatR G).det = 1 := by
  have hb := det_eq_brBlock G h10 h20
  have hB : (brBlock G).det ≠ 0 := by
    intro h0
    rw [hb, h0, mul_zero] at hG
    exact zero_ne_one hG
  unfold levMatR
  rw [Matrix.det_smul, Fintype.card_fin]
  linear_combination hq3 _ hB

@[expose] noncomputable def levHomR (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1) :
    ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 0) →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨levMatR (g.1 : Matrix (Fin 3) (Fin 3) F), det_levMatR hq3 g.1.2
    (CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_zero_iff.mp g.2).1
    (CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_zero_iff.mp g.2).2⟩
  map_one' := Subtype.ext levMatR_one
  map_mul' g h := Subtype.ext (levMatR_mul (CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_zero_iff.mp g.2).1
    (CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_zero_iff.mp g.2).2)

theorem levMatR_scalar {c : F} (hc : c ^ 3 = 1) :
    levMatR (Matrix.scalar (Fin 3) c) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [levMatR, brBlock, Matrix.det_fin_two, Matrix.scalar_apply, Matrix.diagonal_apply] <;>
    linear_combination hc

theorem levHomR_eq_one_of_scalar (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1)
    {g : ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 0)}
    (hg : ((g : Matrix.SpecialLinearGroup (Fin 3) F)) ∈ scalars 3 F) : levHomR hq3 g = 1 := by
  obtain ⟨c, hc, hgc⟩ := mem_scalars.mp hg
  apply Subtype.ext
  show levMatR ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
  rw [hgc]
  apply levMatR_scalar
  rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]

theorem levHomR_eq_one_of_block (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1)
    {g : ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 0)}
    (hb : brBlock ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1) :
    levHomR hq3 g = 1 := by
  apply Subtype.ext
  show levMatR ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
  unfold levMatR
  rw [hb, Matrix.det_one, one_smul]

theorem levHomR_surjective (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1) :
    Function.Surjective (levHomR hq3) := by
  intro B
  have hB := B.2
  rw [Matrix.det_fin_two] at hB
  let M : Matrix (Fin 3) (Fin 3) F :=
    !![1, 0, 0; 0, (B : Matrix (Fin 2) (Fin 2) F) 0 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1;
      0, (B : Matrix (Fin 2) (Fin 2) F) 1 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1]
  have hdet : M.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [M]
    linear_combination hB
  let Mg : Matrix.SpecialLinearGroup (Fin 3) F := ⟨M, hdet⟩
  have hMg : Mg ∈ CFSG.QuasithinUnique.Setup.X7a.Q3 F 0 :=
    CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_zero_iff.mpr ⟨by simp [Mg, M], by simp [Mg, M]⟩
  refine ⟨⟨Mg, hMg⟩, Subtype.ext ?_⟩
  show levMatR M = (B : Matrix (Fin 2) (Fin 2) F)
  have hT : brBlock M = (B : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [brBlock, M]
  unfold levMatR
  rw [hT, B.2, one_smul]

theorem levHomR_eq_one_iff_V1 (hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1)
    (g : ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 0)) :
    levHomR hq3 g = 1 ↔
      proj 3 F (g : Matrix.SpecialLinearGroup (Fin 3) F) ∈
        CFSG.QuasithinUnique.Fin257.L3.V1 := by
  constructor
  · intro h
    obtain ⟨G, hGd⟩ : ∃ G : Matrix (Fin 3) (Fin 3) F,
        G = ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
    have hL : levMatR G = 1 := by rw [hGd]; exact congrArg Subtype.val h
    have hGdet : G.det = 1 := by rw [hGd]; exact (g : Matrix.SpecialLinearGroup (Fin 3) F).2
    obtain ⟨h10, h20⟩ : G 1 0 = 0 ∧ G 2 0 = 0 := by
      rw [hGd]; exact CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_zero_iff.mp g.2
    have hb : G.det = G 0 0 * (brBlock G).det := det_eq_brBlock G h10 h20
    have hδd : G 0 0 * (brBlock G).det = 1 := by rw [← hb, hGdet]
    have hd0 : G 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hδd
    have hLA : (brBlock G).det • brBlock G = 1 := hL
    have e11 : (brBlock G).det * G 1 1 = 1 := by
      have h' := congrFun (congrFun hLA 0) 0
      simpa [brBlock] using h'
    have e22 : (brBlock G).det * G 2 2 = 1 := by
      have h' := congrFun (congrFun hLA 1) 1
      simpa [brBlock] using h'
    have e12 : (brBlock G).det * G 1 2 = 0 := by
      have h' := congrFun (congrFun hLA 0) 1
      simpa [brBlock] using h'
    have e21 : (brBlock G).det * G 2 1 = 0 := by
      have h' := congrFun (congrFun hLA 1) 0
      simpa [brBlock] using h'
    have hδ0 : (brBlock G).det ≠ 0 := right_ne_zero_of_mul_eq_one hδd
    have f11 : G 1 1 = G 0 0 := by linear_combination (G 0 0) * e11 - (G 1 1) * hδd
    have f22 : G 2 2 = G 0 0 := by linear_combination (G 0 0) * e22 - (G 2 2) * hδd
    have f12 : G 1 2 = 0 := (mul_eq_zero.mp e12).resolve_left hδ0
    have f21 : G 2 1 = 0 := (mul_eq_zero.mp e21).resolve_left hδ0
    have he0 : (G 0 0)⁻¹ ≠ 0 := inv_ne_zero hd0
    have he3 : ((G 0 0)⁻¹) ^ 3 = 1 := hq3 _ he0
    let eu : Fˣ := Units.mk0 ((G 0 0)⁻¹) he0
    have heu : eu ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact he3
    let lam : Matrix.SpecialLinearGroup (Fin 3) F := scalarElement eu heu
    have hlam : lam ∈ scalars 3 F := scalarElement_mem_scalars eu heu
    have hlamval : (lam : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) ((G 0 0)⁻¹) :=
      coe_scalarElement eu heu
    have hu : lam * (g : Matrix.SpecialLinearGroup (Fin 3) F) =
        xMat ((G 0 0)⁻¹ * G 0 1) * wMat ((G 0 0)⁻¹ * G 0 2) := by
      apply Subtype.ext
      rw [coe_xMat_mul_wMat, Matrix.SpecialLinearGroup.coe_mul, hlamval, ← hGd]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, Matrix.diagonal_mul, f11, f22, f12, f21, h10, h20,
          inv_mul_cancel₀ hd0]
    have hpu : proj 3 F (lam * (g : Matrix.SpecialLinearGroup (Fin 3) F)) =
        proj 3 F (g : Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [map_mul, proj_eq_one_iff.mpr hlam, one_mul]
    rw [CFSG.QuasithinUnique.Fin257.L3.mem_V1]
    refine ⟨(G 0 0)⁻¹ * G 0 1, (G 0 0)⁻¹ * G 0 2, ?_⟩
    rw [xP, wP, ← map_mul, ← hu, hpu]
  · intro hV
    obtain ⟨a, c, hac⟩ := (CFSG.QuasithinUnique.Fin257.L3.mem_V1).mp hV
    have hpu : proj 3 F (xMat a * wMat c) = proj 3 F (g : Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [map_mul]
      exact hac.symm
    have hu0Q : xMat a * wMat c ∈ CFSG.QuasithinUnique.Setup.X7a.Q3 F 0 :=
      CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_zero_iff.mpr
        ⟨by rw [coe_xMat_mul_wMat]; simp, by rw [coe_xMat_mul_wMat]; simp⟩
    have hsc : (xMat a * wMat c)⁻¹ * (g : Matrix.SpecialLinearGroup (Fin 3) F) ∈ scalars 3 F :=
      proj_eq_proj_iff.mp hpu
    have hlamQ : (xMat a * wMat c)⁻¹ * (g : Matrix.SpecialLinearGroup (Fin 3) F) ∈
        CFSG.QuasithinUnique.Setup.X7a.Q3 F 0 :=
      (CFSG.QuasithinUnique.Setup.X7a.Q3 F 0).mul_mem
        ((CFSG.QuasithinUnique.Setup.X7a.Q3 F 0).inv_mem hu0Q) g.2
    have hgsplit : g = ⟨xMat a * wMat c, hu0Q⟩ *
        ⟨(xMat a * wMat c)⁻¹ * (g : Matrix.SpecialLinearGroup (Fin 3) F), hlamQ⟩ :=
      Subtype.ext (mul_inv_cancel_left _ _).symm
    have hb1 : brBlock ((xMat a * wMat c : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [coe_xMat_mul_wMat]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [brBlock]
    calc levHomR hq3 g
        = levHomR hq3 (⟨xMat a * wMat c, hu0Q⟩ *
            ⟨(xMat a * wMat c)⁻¹ * (g : Matrix.SpecialLinearGroup (Fin 3) F), hlamQ⟩) :=
          congrArg (levHomR hq3) hgsplit
      _ = 1 := by
          rw [map_mul, levHomR_eq_one_of_block (g := ⟨xMat a * wMat c, hu0Q⟩) hq3 hb1,
            levHomR_eq_one_of_scalar (g := ⟨_, hlamQ⟩) hq3 hsc, mul_one]

end PointBlock

section Quotients

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def oTwoQuotNormalizerV2Equiv (hq : Nat.card F = 4) :
    CFSG.Quasithin.oTwoQuot ↥(Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F))) ≃* Matrix.SpecialLinearGroup (Fin 2) F := by
  have hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1 := fun _ hx => cube_eq_one_of_card_four hq hx
  set N := Subgroup.normalizer
    ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) with hNdef
  have hNeq : N = (CFSG.QuasithinUnique.Setup.X7a.Q3 F 1).map (proj 3 F) :=
    CFSG.Quasithin.H13.F431.L3.P3.normalizer_V2_eq
  let q : ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 1) →* ↥N :=
    ((proj 3 F).comp (CFSG.QuasithinUnique.Setup.X7a.Q3 F 1).subtype).codRestrict N
      (fun g => by rw [hNeq]; exact ⟨g.1, g.2, rfl⟩)
  have hqs : Function.Surjective q := by
    rintro ⟨x, hx⟩
    rw [hNeq] at hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨g, hg⟩, rfl⟩
  have hker : q.ker ≤ (levHom hq3).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have h1 : proj 3 F g.1 = 1 := congrArg Subtype.val hg
    exact levHom_eq_one_of_scalar hq3 (proj_eq_one_iff.mp h1)
  let Φ : N →* Matrix.SpecialLinearGroup (Fin 2) F := liftOfComp q hqs (levHom hq3) hker
  have hΦ : ∀ g, Φ (q g) = levHom hq3 g := fun g => liftOfComp_apply q hqs (levHom hq3) hker g
  have hΦs : Function.Surjective Φ := by
    intro y
    obtain ⟨g, hg⟩ := levHom_surjective hq3 y
    exact ⟨q g, by rw [hΦ g, hg]⟩
  have hcore : CFSG.Open.pCoreOf 2 N = CFSG.QuasithinUnique.Fin257.L3.V2 :=
    CFSG.QuasithinUnique.Fin257.L3.core_V2
  have hkerΦ : Φ.ker = CFSG.pCore 2 N := by
    ext x
    obtain ⟨g, rfl⟩ := hqs x
    have hqc' : ((q g : ↥N) : projectiveSL 3 F) = proj 3 F (g : Matrix.SpecialLinearGroup (Fin 3) F) :=
      rfl
    rw [MonoidHom.mem_ker, hΦ g, levHom_eq_one_iff_V2 hq3 g, mem_pCore_iff_mem_pCoreOf, hcore,
      hqc']
  exact (QuotientGroup.quotientMulEquivOfEq hkerΦ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Φ hΦs)

@[expose] noncomputable def oTwoQuotNormalizerV1Equiv (hq : Nat.card F = 4) :
    CFSG.Quasithin.oTwoQuot ↥(Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F))) ≃* Matrix.SpecialLinearGroup (Fin 2) F := by
  have hq3 : ∀ x : F, x ≠ 0 → x ^ 3 = 1 := fun _ hx => cube_eq_one_of_card_four hq hx
  set N := Subgroup.normalizer
    ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) with hNdef
  have hNeq : N = (CFSG.QuasithinUnique.Setup.X7a.Q3 F 0).map (proj 3 F) :=
    CFSG.Quasithin.H13.F431.L3.P3.normalizer_V1_eq
  let q : ↥(CFSG.QuasithinUnique.Setup.X7a.Q3 F 0) →* ↥N :=
    ((proj 3 F).comp (CFSG.QuasithinUnique.Setup.X7a.Q3 F 0).subtype).codRestrict N
      (fun g => by rw [hNeq]; exact ⟨g.1, g.2, rfl⟩)
  have hqs : Function.Surjective q := by
    rintro ⟨x, hx⟩
    rw [hNeq] at hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨g, hg⟩, rfl⟩
  have hker : q.ker ≤ (levHomR hq3).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have h1 : proj 3 F g.1 = 1 := congrArg Subtype.val hg
    exact levHomR_eq_one_of_scalar hq3 (proj_eq_one_iff.mp h1)
  let Φ : N →* Matrix.SpecialLinearGroup (Fin 2) F := liftOfComp q hqs (levHomR hq3) hker
  have hΦ : ∀ g, Φ (q g) = levHomR hq3 g := fun g => liftOfComp_apply q hqs (levHomR hq3) hker g
  have hΦs : Function.Surjective Φ := by
    intro y
    obtain ⟨g, hg⟩ := levHomR_surjective hq3 y
    exact ⟨q g, by rw [hΦ g, hg]⟩
  have hcore : CFSG.Open.pCoreOf 2 N = CFSG.QuasithinUnique.Fin257.L3.V1 :=
    CFSG.QuasithinUnique.Fin257.L3.core_V1
  have hkerΦ : Φ.ker = CFSG.pCore 2 N := by
    ext x
    obtain ⟨g, rfl⟩ := hqs x
    have hqc' : ((q g : ↥N) : projectiveSL 3 F) = proj 3 F (g : Matrix.SpecialLinearGroup (Fin 3) F) :=
      rfl
    rw [MonoidHom.mem_ker, hΦ g, levHomR_eq_one_iff_V1 hq3 g, mem_pCore_iff_mem_pCoreOf, hcore,
      hqc']
  exact (QuotientGroup.quotientMulEquivOfEq hkerΦ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Φ hΦs)

end Quotients

theorem isL2Quot_normalizer_V2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : Nat.card F = 4) :
    CFSG.Quasithin.IsL2Quot 2 (CFSG.Quasithin.oTwoQuot ↥(Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)))) := by
  unfold CFSG.Quasithin.IsL2Quot
  have eF : F ≃+* GaloisField 2 2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 2 (by norm_num) (by rw [hq]; norm_num)
  exact ⟨(oTwoQuotNormalizerV2Equiv hq).trans
    ((CFSG.ClassicalModels.specialLinearFieldEquiv eF (Fin 2)).trans
      ((projectiveSpecialLinearEquivProjectiveSL 2 (GaloisField 2 2)).trans
        (projectiveSLTwoEquivSL (GaloisField 2 2))).symm)⟩

theorem isL2Quot_normalizer_V1 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : Nat.card F = 4) :
    CFSG.Quasithin.IsL2Quot 2 (CFSG.Quasithin.oTwoQuot ↥(Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)))) := by
  unfold CFSG.Quasithin.IsL2Quot
  have eF : F ≃+* GaloisField 2 2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 2 (by norm_num) (by rw [hq]; norm_num)
  exact ⟨(oTwoQuotNormalizerV1Equiv hq).trans
    ((CFSG.ClassicalModels.specialLinearFieldEquiv eF (Fin 2)).trans
      ((projectiveSpecialLinearEquivProjectiveSL 2 (GaloisField 2 2)).trans
        (projectiveSLTwoEquivSL (GaloisField 2 2))).symm)⟩

theorem pCoreOf_normalizer_V2 {F : Type} [Field F] [Finite F] [CharP F 2] :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F))) = CFSG.QuasithinUnique.Fin257.L3.V2 :=
  CFSG.QuasithinUnique.Fin257.L3.core_V2

theorem pCoreOf_normalizer_V1 {F : Type} [Field F] [Finite F] [CharP F 2] :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F))) = CFSG.QuasithinUnique.Fin257.L3.V1 :=
  CFSG.QuasithinUnique.Fin257.L3.core_V1

theorem natCard_oTwoQuot_normalizer_V2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : Nat.card F = 4) :
    Nat.card (CFSG.Quasithin.oTwoQuot ↥(Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)))) = 60 := by
  rw [Nat.card_congr (oTwoQuotNormalizerV2Equiv hq).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq]
  norm_num

theorem natCard_oTwoQuot_normalizer_V1 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : Nat.card F = 4) :
    Nat.card (CFSG.Quasithin.oTwoQuot ↥(Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)))) = 60 := by
  rw [Nat.card_congr (oTwoQuotNormalizerV1Equiv hq).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq]
  norm_num

end CFSG.GH74.QTGen4.DSGen4.L34
