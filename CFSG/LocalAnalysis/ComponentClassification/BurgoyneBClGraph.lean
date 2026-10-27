module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClForms
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClEmb

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.Burgoyne.PSL (graphLift conjAut_mul_dualAut_proj isometrySL
  graphLift_eq_iff inv_transpose_of_transpose_eq_neg vecMul_dotProduct_self_of_alt
  exists_vecMul_ne_zero inv_transpose_of_transpose_eq conjAut_mul_conjAut_dualAut_mul_inv
  exists_frame diagGL coe_diagGL isoOrthGL isQuasisimple_trans trans_commutator
  map_comap_toGL_of_le_commutator det_eq_one_of_mem_commutator)
open CFSG.ComponentClassification.CatLeafProof.EndOddLin (QuatBlock quatBlock_map_of_sl2)
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K]

theorem fixOf_graphLift (A : GL (Fin n) K) : fixOf (graphLift A) = isometrySL n A⁻¹ := by
  ext g
  exact graphLift_eq_iff A g

section Symp

variable [Finite K]

omit [Finite K] in
theorem exists_hyperbolic_pair (hn : 1 ≤ n) (R : GL (Fin n) K) :
    ∃ e f : Fin n → K, e ⬝ᵥ ((R : Matrix (Fin n) (Fin n) K) *ᵥ f) = 1 := by
  set e : Fin n → K := Pi.single ⟨0, hn⟩ 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hn⟩
    simp [he] at this
  obtain ⟨b, hb⟩ := exists_vecMul_ne_zero R he0
  refine ⟨e, ((e ᵥ* (R : Matrix (Fin n) (Fin n) K)) b)⁻¹ • Pi.single b 1, ?_⟩
  rw [dotProduct_mulVec, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul,
    inv_mul_cancel₀ hb]

theorem isQuasisimple_isometryGroup_alt (hK : ringChar K ≠ 2) (hn : 4 ≤ n) {R : GL (Fin n) K}
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) :
    IsQuasisimple (CatalogueBGraphForm.isometryGroup n K R) :=
  LocalCores.isQuasisimple_of_mulEquiv (CatalogueBLinearHigherB.isometryGroupEquiv R)
    (CatalogueBAlternatingIsometry.isometry_quasisimple_of_four_le _
      (CatalogueBLinearHigherB.matrixForm_isAlt hK R hR)
      (CatalogueBLinearHigherB.matrixForm_nondegenerate R)
      (by rwa [Module.finrank_fin_fun])
      (CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK))

theorem det_eq_one_of_mem_isometryGroup_alt (hK : ringChar K ≠ 2) (hn : 4 ≤ n)
    {R : GL (Fin n) K}
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) {G : GL (Fin n) K}
    (hG : G ∈ CatalogueBGraphForm.isometryGroup n K R) :
    (G : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hI := isQuasisimple_isometryGroup_alt hK hn hR
  have hperf : commutator (CatalogueBGraphForm.isometryGroup n K R) = ⊤ :=
    hI.1.commutator_eq_top
  have hle : commutator (CatalogueBGraphForm.isometryGroup n K R) ≤
      (GeneralLinearGroup.det.comp (CatalogueBGraphForm.isometryGroup n K R).subtype).ker :=
    Abelianization.commutator_subset_ker _
  have h1 := hle (hperf ▸ mem_top (⟨G, hG⟩ : CatalogueBGraphForm.isometryGroup n K R))
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff,
    GeneralLinearGroup.val_det_apply, Units.val_one] at h1
  exact h1

theorem isQuasisimple_isometrySL_alt (hK : ringChar K ≠ 2) (hn : 4 ≤ n) {R : GL (Fin n) K}
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) :
    IsQuasisimple (isometrySL n R) := by
  have hmap : (isometrySL n R).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup n K R := by
    ext G
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hG
      have hGe : SpecialLinearGroup.toGL
          (⟨(G : Matrix (Fin n) (Fin n) K), det_eq_one_of_mem_isometryGroup_alt hK hn hR hG⟩ :
            SpecialLinearGroup (Fin n) K) = G :=
        Units.ext rfl
      refine ⟨_, ?_, hGe⟩
      show _ ∈ isometrySL n R
      exact Subgroup.mem_comap.2 (by rw [hGe]; exact hG)
  exact LocalCores.isQuasisimple_of_mulEquiv (((isometrySL n R).equivMapOfInjective _
    SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmap)).symm
    (isQuasisimple_isometryGroup_alt hK hn hR)

omit [Finite K] in
theorem mem_isometrySL_iff {R : GL (Fin n) K} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ isometrySL n R ↔
      (g : Matrix (Fin n) (Fin n) K)ᵀ * R * g = (R : Matrix (Fin n) (Fin n) K) := by
  rw [mem_comap, CatalogueBGraphForm.mem_isometryGroup]
  rfl

omit [Finite K] in
theorem not_mem_scalars_of_ne_smul {g : SpecialLinearGroup (Fin n) K}
    (h : ∀ c : K, (g : Matrix (Fin n) (Fin n) K) ≠ c • 1) : g ∉ scalars n K := by
  rintro ⟨c, -, hc⟩
  exact h c (by rw [hc, scalar_apply, smul_one_eq_diagonal])

theorem quatBlock_isometrySL_alt (hK : ringChar K ≠ 2) (hn : 4 ≤ n) {R : GL (Fin n) K}
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) :
    QuatBlock ((isometrySL n R).map (QuotientGroup.mk' (scalars n K))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨e, f, hef⟩ := exists_hyperbolic_pair (by omega) R
  obtain ⟨E, F, hFE, h1, h2'⟩ := alt_emb h2 hR hef
  refine quatBlock_map_of_sl2 (isQuasisimple_isometrySL_alt hK hn hR) hK (embSL hFE)
    (fun g => ?_) (not_mem_scalars_of_ne_smul fun c hc => ?_)
  · rw [mem_isometrySL_iff, coe_embSL]
    exact embT_isometry hFE h1 h2' (transpose_J₂_mul g)
  · rw [coe_embSL, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at hc
    exact embT_neg_one_ne_smul h2 hFE (by simp; omega) c hc

theorem noL2At_conj_dual_alt (hK : ringChar K ≠ 2) (hn : 3 ≤ n) {A : GL (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = -(A : Matrix (Fin n) (Fin n) K)) :
    NoL2At (conjAut n K A * dualAut n K) := by
  have hR := inv_transpose_of_transpose_eq_neg A hA
  have hn4 : 4 ≤ n := by
    have hev := CatalogueBAlternatingIsometry.even_finrank _
      (CatalogueBLinearHigherB.matrixForm_isAlt hK A⁻¹ hR)
      (CatalogueBLinearHigherB.matrixForm_nondegenerate A⁻¹)
    rw [Module.finrank_fin_fun] at hev
    obtain ⟨k, hk⟩ := hev
    omega
  refine noL2At_of_fix (scalars_le_center n K) (conjAut_mul_dualAut_proj A) ?_
  rw [fixOf_graphLift]
  exact quatBlock_isometrySL_alt hK hn4 hR

end Symp

section Orth

variable [Finite K]

theorem isQuasisimple_orthCommutator (hK : ringChar K ≠ 2) (hn : 6 ≤ n) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) :
    IsQuasisimple (⁅CatalogueBGraphForm.isometryGroup n K R,
      CatalogueBGraphForm.isometryGroup n K R⁆ : Subgroup (GL (Fin n) K)) := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have key : IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    by_cases hT : ∃ T : Submodule K (Fin n → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
    · obtain ⟨T, hT3, hTQ⟩ := hT
      exact CatalogueBOrthogonal.derived_quasisimple Q h2 hQnd hT3.ge hTQ
    · have hcases := CatalogueBOrthogonalAssembly.low_Witt_finrank_cases hodd Q hQnd
        (by rw [hdim]; omega) hT
      have h6 : Module.finrank K (Fin n → K) = 6 := by
        rw [hdim] at hcases ⊢
        omega
      obtain ⟨-, -, -, -, -, -, h7⟩ :=
        LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
          Q hQnd (Or.inr (Or.inl ⟨hodd, h6, hT⟩))
      obtain ⟨-, -, -, -, -, -, -, -, hq⟩ := h7 hodd h6 hT
      exact hq
  have hq' := isQuasisimple_trans (isoOrthGL hK R hR) key
  rwa [trans_commutator] at hq'

abbrev orthLayerSL (R : GL (Fin n) K) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  Subgroup.comap SpecialLinearGroup.toGL
    ⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆

omit [Finite K] in
theorem exists_orth_quat_pair (h2 : (2 : K) ≠ 0) (hn : 5 ≤ n) {R : GL (Fin n) K}
    {E : Matrix (Fin n) (Fin 4) K} {F : Matrix (Fin 4) (Fin n) K} (hFE : F * E = 1)
    (hc1 : Eᵀ * (R : Matrix (Fin n) (Fin n) K) = (1 : Matrix (Fin 4) (Fin 4) K) * F)
    (hc2 : (R : Matrix (Fin n) (Fin n) K) * E = Fᵀ * (1 : Matrix (Fin 4) (Fin 4) K)) :
    ∃ X Y Z : GL (Fin n) K,
      X ∈ ⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆ ∧
      Y ∈ ⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆ ∧
      Z ^ 2 = 1 ∧ X ^ 2 = Z ∧ Y ^ 2 = Z ∧ X * Y = Z * (Y * X) ∧
      ∀ c : K, (Z : Matrix (Fin n) (Fin n) K) ≠ c • 1 := by
  set I := CatalogueBGraphForm.isometryGroup n K R with hI
  set T : GL (Fin 4) K →* GL (Fin n) K := Units.map (embHom hFE) with hT
  have hTv : ∀ g : GL (Fin 4) K, ((T g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      embT E F g := fun g => rfl
  set I₄ := CatalogueBGraphForm.isometryGroup 4 K 1 with hI₄
  have hTI : I₄.map T ≤ I := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
    have hg' := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 hg
    refine (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 ?_
    rw [hTv]
    exact embT_isometry hFE hc1 hc2 (by simpa using hg')
  have hTΩ : (⁅I₄, I₄⁆).map T ≤ ⁅I, I⁆ := by
    rw [map_commutator]
    exact commutator_mono hTI hTI
  have hXX := quatI_sq (K := K)
  have hYY := quatJ_sq (K := K)
  have hYX := quatJ_mul_quatI (K := K)
  set uX : GL (Fin 4) K := ⟨quatI, -quatI, by rw [Matrix.mul_neg, hXX, neg_neg],
    by rw [Matrix.neg_mul, hXX, neg_neg]⟩ with huX
  set uY : GL (Fin 4) K := ⟨quatJ, -quatJ, by rw [Matrix.mul_neg, hYY, neg_neg],
    by rw [Matrix.neg_mul, hYY, neg_neg]⟩ with huY
  set uW : GL (Fin 4) K := ⟨quatW quatI quatJ, quatW' quatI quatJ,
    quatW_mul_quatW' hXX hYY hYX h2, quatW'_mul_quatW hXX hYY hYX h2⟩ with huW
  have hXI : uX ∈ I₄ := by
    rw [CatalogueBGraphForm.mem_isometryGroup]
    exact quatI_orth
  have hYI : uY ∈ I₄ := by
    rw [CatalogueBGraphForm.mem_isometryGroup]
    exact quatJ_orth
  have hWI : uW ∈ I₄ := by
    rw [CatalogueBGraphForm.mem_isometryGroup]
    exact quatW_isometry hXX hYY hYX h2 quatI_orth quatJ_orth
  have hz2 : (-1 : GL (Fin 4) K) ^ 2 = 1 := by rw [neg_one_sq]
  have hx2 : uX ^ 2 = -1 := Units.ext (by rw [pow_two]; exact hXX)
  have hy2 : uY ^ 2 = -1 := Units.ext (by rw [pow_two]; exact hYY)
  have hxy : uX * uY = -1 * (uY * uX) := Units.ext (by
    change quatI * quatJ = ((-1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (quatJ * quatI)
    rw [Units.val_neg, Units.val_one, Matrix.neg_mul, Matrix.one_mul, hYX, neg_neg])
  have hw1 : uW * uY * uW⁻¹ = uX * uY := Units.ext (by
    change quatW quatI quatJ * quatJ * quatW' quatI quatJ = quatI * quatJ
    rw [quatW_mul_y hXX hYY hYX, Matrix.mul_assoc, quatW_mul_quatW' hXX hYY hYX h2,
      Matrix.mul_one])
  have hw2 : uW * (uX * uY) * uW⁻¹ = uX := Units.ext (by
    change quatW quatI quatJ * (quatI * quatJ) * quatW' quatI quatJ = quatI
    rw [quatW_mul_xy hXX hYY hYX, Matrix.mul_assoc, quatW_mul_quatW' hXX hYY hYX h2,
      Matrix.mul_one])
  obtain ⟨hcX, hcY⟩ := commutatorElement_quat hz2 hx2 hy2 hxy hw1 hw2
  have hXc : uX ∈ ⁅I₄, I₄⁆ := hcX ▸ commutator_mem_commutator hWI hYI
  have hYc : uY ∈ ⁅I₄, I₄⁆ := hcY ▸ commutator_mem_commutator hWI (mul_mem hXI hYI)
  refine ⟨T uX, T uY, T (-1), hTΩ ⟨uX, hXc, rfl⟩, hTΩ ⟨uY, hYc, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hz2, map_one]
  · rw [← map_pow, hx2]
  · rw [← map_pow, hy2]
  · rw [← map_mul, hxy, map_mul, map_mul]
  · intro c hc
    rw [hTv, Units.val_neg, Units.val_one] at hc
    exact embT_neg_one_ne_smul h2 hFE (by simp; omega) c hc

theorem quatBlock_orthLayerSL (hK : ringChar K ≠ 2) (hn : 6 ≤ n) {R : GL (Fin n) K}
    (hRs : (R : Matrix (Fin n) (Fin n) K)ᵀ = R)
    {E : Matrix (Fin n) (Fin 4) K} {F : Matrix (Fin 4) (Fin n) K} (hFE : F * E = 1)
    (hc1 : Eᵀ * (R : Matrix (Fin n) (Fin n) K) = (1 : Matrix (Fin 4) (Fin 4) K) * F)
    (hc2 : (R : Matrix (Fin n) (Fin n) K) * E = Fᵀ * (1 : Matrix (Fin 4) (Fin 4) K)) :
    QuatBlock ((orthLayerSL R).map (QuotientGroup.mk' (scalars n K))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set I := CatalogueBGraphForm.isometryGroup n K R with hI
  set Ω := ⁅I, I⁆ with hΩ
  have hq : IsQuasisimple (orthLayerSL R) := by
    have hmap : (orthLayerSL R).map SpecialLinearGroup.toGL = Ω :=
      map_comap_toGL_of_le_commutator le_rfl
    exact LocalCores.isQuasisimple_of_mulEquiv (((orthLayerSL R).equivMapOfInjective _
      SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmap)).symm
      (isQuasisimple_orthCommutator hK hn R hRs)
  obtain ⟨X, Y, Z, hX, hY, hz2, hxz, hyz, hxy, hZ⟩ :=
    exists_orth_quat_pair h2 (by omega) hFE hc1 hc2
  have hZΩ : Z ∈ Ω := hxz ▸ pow_mem hX 2
  set x : SpecialLinearGroup (Fin n) K := ⟨X, det_eq_one_of_mem_commutator hX⟩ with hx
  set y : SpecialLinearGroup (Fin n) K := ⟨Y, det_eq_one_of_mem_commutator hY⟩ with hy
  set z : SpecialLinearGroup (Fin n) K := ⟨Z, det_eq_one_of_mem_commutator hZΩ⟩ with hz
  have hxm : x ∈ orthLayerSL R := by
    change SpecialLinearGroup.toGL x ∈ Ω
    rw [show SpecialLinearGroup.toGL x = X from Units.ext rfl]
    exact hX
  have hym : y ∈ orthLayerSL R := by
    change SpecialLinearGroup.toGL y ∈ Ω
    rw [show SpecialLinearGroup.toGL y = Y from Units.ext rfl]
    exact hY
  have hval : ∀ {a : SpecialLinearGroup (Fin n) K} {b : GL (Fin n) K},
      (a : Matrix (Fin n) (Fin n) K) = b → SpecialLinearGroup.toGL a = b := fun h => Units.ext h
  refine quatBlock_map_of_pair hq hxm hym (z := z) ?_ ?_ ?_ ?_
    (not_mem_scalars_of_ne_smul fun c hc => hZ c hc)
  · apply SpecialLinearGroup.toGL_injective
    rw [map_pow, map_one, hval rfl, hz2]
  · apply SpecialLinearGroup.toGL_injective
    rw [map_pow, hval rfl, hval rfl, hxz]
  · apply SpecialLinearGroup.toGL_injective
    rw [map_pow, hval rfl, hval rfl, hyz]
  · apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_mul, hval rfl, hval rfl, hval rfl, hxy]

theorem noL2At_conj_dual_diag (hK : ringChar K ≠ 2) (hn : 6 ≤ n) {w : Fin n → K}
    (hw0 : ∀ i, w i ≠ 0) (hw1 : ∀ a : Fin 4, w (Fin.castLE (by omega) a) = 1) :
    NoL2At (conjAut n K (diagGL hw0)⁻¹ * dualAut n K) := by
  set D := diagGL hw0 with hD
  set I := CatalogueBGraphForm.isometryGroup n K D with hI
  have hfix : fixOf (graphLift D⁻¹) = I.comap SpecialLinearGroup.toGL := by
    rw [fixOf_graphLift, inv_inv]
  have h4 : 4 ≤ n := by omega
  have hDm : (D : Matrix (Fin n) (Fin n) K) = diagonal w := coe_diagGL hw0
  have hDs : (D : Matrix (Fin n) (Fin n) K)ᵀ = D := by rw [hDm, diagonal_transpose]
  have hc1 := coord4_transpose_mul_diag h4 hw1
  have hc2 := diag_mul_coord4 h4 hw1
  rw [← hDm] at hc1 hc2
  refine noL2At_of_fix_layer (scalars_le_center n K) (conjAut_mul_dualAut_proj D⁻¹)
    (F := orthLayerSL D) ?_ ?_
    (quatBlock_orthLayerSL hK hn hDs (coord4_transpose_mul h4) hc1 hc2)
  · rw [hfix]
    exact comap_mono (commutator_le_self' I)
  · rw [hfix, commutator_le]
    intro a ha b hb
    change SpecialLinearGroup.toGL ⁅a, b⁆ ∈ ⁅I, I⁆
    rw [map_commutatorElement]
    exact commutator_mem_commutator ha hb

theorem noL2At_conj_dual_sym (hK : ringChar K ≠ 2) (hn : 6 ≤ n) {A : GL (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = A) : NoL2At (conjAut n K A * dualAut n K) := by
  have hR := inv_transpose_of_transpose_eq A hA
  obtain ⟨P, w, hw0, hw1, hP⟩ := exists_frame hK (by omega) A⁻¹ hR one_ne_zero
  set H := P⁻¹ with hH
  have hHA : H * A * GeneralLinearGroup.inverseTranspose H⁻¹ = (diagGL hw0)⁻¹ := by
    have hT : CatalogueBGraphForm.glTranspose n K P * A⁻¹ * P = diagGL hw0 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, CatalogueBGraphForm.glTranspose_matrix, coe_diagGL]
      exact hP
    have hT' : CatalogueBGraphForm.glTranspose n K P =
        (GeneralLinearGroup.inverseTranspose P)⁻¹ := rfl
    rw [← hT, hT', hH, inv_inv]
    group
  refine NoL2At.of_conj (conjAut n K H) ?_
  rw [conjAut_mul_conjAut_dualAut_mul_inv, hHA]
  exact noL2At_conj_dual_diag hK hn hw0 fun a => hw1 _ (by simp; omega)

end Orth

end CFSG.ComponentClassification.Burgoyne.Cl
