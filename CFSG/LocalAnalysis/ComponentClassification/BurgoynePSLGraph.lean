module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem conjAut_eq_one_of_eq_scalar {D : GL (Fin n) K} (a : Fin n)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) ((D : Matrix _ _ K) a a)) :
    conjAut n K D = 1 := by
  have h0 : (D : Matrix (Fin n) (Fin n) K) a a ≠ 0 := by
    intro h0
    have hdet : IsUnit (D : Matrix (Fin n) (Fin n) K).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
    have hD0 : (D : Matrix (Fin n) (Fin n) K) = 0 := by
      rw [hD, h0, map_zero]
    have : Nonempty (Fin n) := ⟨a⟩
    rw [hD0, det_zero] at hdet
    exact not_isUnit_zero hdet
  have hDs : D = GeneralLinearGroup.scalar (Fin n) (Units.mk0 _ h0) := Units.ext (hD.trans rfl)
  rw [hDs, conjAut_scalar]

theorem exists_eigen_of_commute_vecMulVec {D : Matrix (Fin n) (Fin n) K} {v w : Fin n → K}
    {b : Fin n} (hb : w b ≠ 0) (h : D * vecMulVec v w = vecMulVec v w * D) :
    ∃ μ : K, D *ᵥ v = μ • v := by
  rw [mul_vecMulVec, vecMulVec_mul] at h
  refine ⟨(w ᵥ* D) b / w b, ?_⟩
  ext a
  have := congrFun (congrFun h a) b
  simp only [vecMulVec_apply] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination this

theorem eq_scalar_of_eigen {D : Matrix (Fin n) (Fin n) K} (a : Fin n)
    (h : ∀ v : Fin n → K, ∃ μ : K, D *ᵥ v = μ • v) : D = Matrix.scalar (Fin n) (D a a) := by
  have hcol : ∀ i j, i ≠ j → D i j = 0 := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := h (Pi.single j 1)
    have := congrFun hμ i
    simp only [mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_apply, hij,
      ↓reduceIte, smul_zero] at this
    simpa using this
  have hdiag : ∀ i j, D i i = D j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨μ, hμ⟩ := h (Pi.single i 1 + Pi.single j 1)
    have hi := congrFun hμ i
    have hj := congrFun hμ j
    simp only [mulVec_add, mulVec_single_one, Matrix.col_apply, Pi.add_apply, Pi.smul_apply,
      Pi.single_apply, hij, Ne.symm hij, ↓reduceIte, smul_eq_mul] at hi hj
    rw [hcol i j hij] at hi
    rw [hcol j i (Ne.symm hij)] at hj
    simp only [add_zero, zero_add, mul_one] at hi hj
    rw [hi, hj]
  ext i j
  rw [scalar_apply, diagonal_apply]
  split_ifs with hij
  · rw [hij, hdiag j a]
  · exact hcol i j hij

@[expose] def graphLift (A : GL (Fin n) K) :
    SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K :=
  (CatalogueBHigherLinearAction.slConjugation n K A).toMonoidHom.comp
    (CatalogueBGraphForm.slGraphAut n K).toMonoidHom

theorem conjAut_mul_dualAut_proj (A : GL (Fin n) K) (g : SpecialLinearGroup (Fin n) K) :
    (conjAut n K A * dualAut n K) (proj n K g) = proj n K (graphLift A g) := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
  rfl

theorem toGL_graphLift (A : GL (Fin n) K) (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.toGL (graphLift A g) =
      A * GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL g) * A⁻¹ := by
  change SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation n K A
    (CatalogueBGraphForm.slGraphAut n K g)) = _
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut]

variable (n) in
abbrev isometrySL (R : GL (Fin n) K) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  (CatalogueBGraphForm.isometryGroup n K R).comap SpecialLinearGroup.toGL

theorem graphLift_eq_iff (A : GL (Fin n) K) (g : SpecialLinearGroup (Fin n) K) :
    graphLift A g = g ↔ g ∈ isometrySL n A⁻¹ := by
  rw [← SpecialLinearGroup.toGL_injective.eq_iff, toGL_graphLift]
  change _ ↔ CatalogueBGraphForm.glTranspose n K (SpecialLinearGroup.toGL g) * A⁻¹ *
    SpecialLinearGroup.toGL g = A⁻¹
  set G := SpecialLinearGroup.toGL g
  have hT : CatalogueBGraphForm.glTranspose n K G =
      (GeneralLinearGroup.inverseTranspose G)⁻¹ := rfl
  rw [hT]
  set X := GeneralLinearGroup.inverseTranspose G
  constructor
  · intro h
    rw [← h]
    group
  · intro h
    calc A * X * A⁻¹ = A * X * (X⁻¹ * A⁻¹ * G) := by rw [h]
      _ = G := by group

theorem conj_mem_isometrySL (A : GL (Fin n) K) {h : SpecialLinearGroup (Fin n) K}
    (hh : h⁻¹ * graphLift A h ∈ scalars n K) {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ isometrySL n A⁻¹) : h * g * h⁻¹ ∈ isometrySL n A⁻¹ := by
  rw [← graphLift_eq_iff]
  exact conj_mem_eqLocus_of_scalar (graphLift A) hh ((graphLift_eq_iff A g).2 hg)

theorem det_one_add_smul_vecMulVec {v w : Fin n → K} (hvw : w ⬝ᵥ v = 0) (c : K) :
    (1 + c • vecMulVec v w).det = 1 := by
  have e : c • vecMulVec v w = replicateCol Unit (c • v) * replicateRow Unit w := by
    rw [← vecMulVec_eq Unit]
    ext i j
    simp [vecMulVec_apply, mul_assoc]
  rw [e, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hvw, smul_zero, add_zero]

@[expose] def unipSL {v w : Fin n → K} (hvw : w ⬝ᵥ v = 0) (c : K) :
    SpecialLinearGroup (Fin n) K :=
  ⟨1 + c • vecMulVec v w, det_one_add_smul_vecMulVec hvw c⟩

theorem coe_unipSL {v w : Fin n → K} (hvw : w ⬝ᵥ v = 0) (c : K) :
    ((unipSL hvw c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + c • vecMulVec v w := rfl

theorem vecMulVec_mul_self {v w : Fin n → K} (hvw : w ⬝ᵥ v = 0) :
    vecMulVec v w * vecMulVec v w = 0 := by
  rw [vecMulVec_mul_vecMulVec, hvw, zero_smul, vecMulVec_zero]

theorem exists_vecMul_ne_zero (R : GL (Fin n) K) {v : Fin n → K} (hv : v ≠ 0) :
    ∃ b, (v ᵥ* (R : Matrix (Fin n) (Fin n) K)) b ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  have h0 : v ᵥ* (R : Matrix (Fin n) (Fin n) K) = 0 := funext h
  have : v ᵥ* (R : Matrix (Fin n) (Fin n) K) ᵥ* ((R⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = v := by
    rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  rw [← this, h0, zero_vecMul]

theorem inv_transpose_of_transpose_eq_neg (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = -(A : Matrix (Fin n) (Fin n) K)) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      -((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
      (A : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  calc ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ
      = (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
          (A : Matrix (Fin n) (Fin n) K)) * (A⁻¹ : GL (Fin n) K) := by
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    _ = (-(((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
          (A : Matrix (Fin n) (Fin n) K)ᵀ)) * (A⁻¹ : GL (Fin n) K) := by
        rw [hA, Matrix.mul_neg, neg_neg]
    _ = -((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [h, Matrix.neg_mul, Matrix.one_mul]

theorem vecMul_dotProduct_self_of_alt (hK : ringChar K ≠ 2) {R : GL (Fin n) K}
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) (v : Fin n → K) :
    (v ᵥ* (R : Matrix (Fin n) (Fin n) K)) ⬝ᵥ v = 0 := by
  have h := CatalogueBLinearHigherB.matrixForm_isAlt hK R hR v
  rw [CatalogueBLinearHigherB.matrixForm_apply, dotProduct_mulVec] at h
  exact h

theorem symTransv_mem (hK : ringChar K ≠ 2) {R : GL (Fin n) K}
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) (v : Fin n → K)
    (c : K) : unipSL (vecMul_dotProduct_self_of_alt hK hR v) c ∈ isometrySL n R := by
  rw [mem_comap, CatalogueBGraphForm.mem_isometryGroup]
  change (1 + c • vecMulVec v (v ᵥ* (R : Matrix (Fin n) (Fin n) K)))ᵀ *
    (R : Matrix (Fin n) (Fin n) K) * (1 + c • vecMulVec v (v ᵥ* (R : Matrix (Fin n) (Fin n) K))) =
      (R : Matrix (Fin n) (Fin n) K)
  set w := v ᵥ* (R : Matrix (Fin n) (Fin n) K) with hw
  have hRv : (R : Matrix (Fin n) (Fin n) K) *ᵥ v = -w := by
    rw [hw, ← mulVec_transpose, hR, neg_mulVec, neg_neg]
  have hwv : w ⬝ᵥ v = 0 := vecMul_dotProduct_self_of_alt hK hR v
  have e1 : (vecMulVec v w)ᵀ * (R : Matrix (Fin n) (Fin n) K) = vecMulVec w w := by
    rw [transpose_vecMulVec, vecMulVec_mul]
  have e2 : (R : Matrix (Fin n) (Fin n) K) * vecMulVec v w = -vecMulVec w w := by
    rw [mul_vecMulVec, hRv]
    ext i j
    simp [vecMulVec_apply]
  have e3 : vecMulVec w w * vecMulVec v w = 0 := by
    rw [vecMulVec_mul_vecMulVec, hwv, zero_smul, vecMulVec_zero]
  have hexp : ((1 : Matrix (Fin n) (Fin n) K) + c • (vecMulVec v w)ᵀ) *
      (R : Matrix (Fin n) (Fin n) K) * (1 + c • vecMulVec v w) =
      (R : Matrix (Fin n) (Fin n) K) + c • ((vecMulVec v w)ᵀ * (R : Matrix (Fin n) (Fin n) K) +
        (R : Matrix (Fin n) (Fin n) K) * vecMulVec v w) +
        (c * c) • ((vecMulVec v w)ᵀ * (R : Matrix (Fin n) (Fin n) K) * vecMulVec v w) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul]
    abel
  rw [transpose_add, transpose_one, transpose_smul, hexp, e1, e2, add_neg_cancel, smul_zero,
    add_zero, e3, smul_zero, add_zero]

theorem isQuasisimple_isometrySL_alt [Finite K] (hK : ringChar K ≠ 2) (hn : 4 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {R : GL (Fin n) K}
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) :
    IsQuasisimple ((isometrySL n R).map (conjProj n K)) := by
  have hI : IsQuasisimple (CatalogueBGraphForm.isometryGroup n K R) :=
    LocalCores.isQuasisimple_of_mulEquiv (CatalogueBLinearHigherB.isometryGroupEquiv R)
      (CatalogueBAlternatingIsometry.isometry_quasisimple_of_four_le _
        (CatalogueBLinearHigherB.matrixForm_isAlt hK R hR)
        (CatalogueBLinearHigherB.matrixForm_nondegenerate R)
        (by rwa [Module.finrank_fin_fun])
        (CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK))
  have hdet : ∀ G ∈ CatalogueBGraphForm.isometryGroup n K R,
      (G : Matrix (Fin n) (Fin n) K).det = 1 := by
    intro G hG
    have hperf : commutator (CatalogueBGraphForm.isometryGroup n K R) = ⊤ :=
      hI.1.commutator_eq_top
    have hle : commutator (CatalogueBGraphForm.isometryGroup n K R) ≤
        (GeneralLinearGroup.det.comp (CatalogueBGraphForm.isometryGroup n K R).subtype).ker :=
      Abelianization.commutator_subset_ker _
    have h1 := hle (hperf ▸ mem_top (⟨G, hG⟩ : CatalogueBGraphForm.isometryGroup n K R))
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff,
      GeneralLinearGroup.val_det_apply, Units.val_one] at h1
    exact h1
  have hmap : (isometrySL n R).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup n K R := by
    ext G
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hG
      have hGe : SpecialLinearGroup.toGL
          (⟨(G : Matrix (Fin n) (Fin n) K), hdet G hG⟩ : SpecialLinearGroup (Fin n) K) = G :=
        Units.ext rfl
      refine ⟨_, ?_, hGe⟩
      show _ ∈ isometrySL n R
      exact Subgroup.mem_comap.2 (by rw [hGe]; exact hG)
  have hF : IsQuasisimple (isometrySL n R) :=
    LocalCores.isQuasisimple_of_mulEquiv (((isometrySL n R).equivMapOfInjective _
      SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmap)).symm hI
  refine LocalCores.isQuasisimple_map hF _ fun hle => ?_
  have hv : (Pi.single ⟨0, by omega⟩ 1 : Fin n → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  obtain ⟨b, hb⟩ := exists_vecMul_ne_zero R hv
  have hmem := symTransv_mem hK hR (Pi.single ⟨0, by omega⟩ 1) 1
  have hker := hle hmem
  have hproj : proj n K (unipSL (vecMul_dotProduct_self_of_alt hK hR
      (Pi.single ⟨0, by omega⟩ 1)) 1) = 1 := hinj (by rw [map_one]; exact hker)
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 hproj
  have hN := vecMulVec_mul_self (vecMul_dotProduct_self_of_alt hK hR
    (Pi.single (⟨0, by omega⟩ : Fin n) (1 : K)))
  set N := vecMulVec (Pi.single (⟨0, by omega⟩ : Fin n) (1 : K))
    (Pi.single (⟨0, by omega⟩ : Fin n) (1 : K) ᵥ* (R : Matrix (Fin n) (Fin n) K)) with hNdef
  have hc' : (1 : Matrix (Fin n) (Fin n) K) + N = Matrix.scalar (Fin n) (c : K) := by
    rw [← hc, coe_unipSL, one_smul]
  have hN' : N = Matrix.scalar (Fin n) ((c : K) - 1) := by
    rw [map_sub, ← hc', map_one]
    abel
  rw [hN', ← map_mul] at hN
  have hc1 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
    have := congrFun (congrFun hN ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using this
  have hN0 : N = 0 := by
    rw [hN', mul_self_eq_zero.1 hc1, map_zero]
  have := congrFun (congrFun hN0 ⟨0, by omega⟩) b
  simp only [hNdef, vecMulVec_apply, Pi.single_eq_same, one_mul, Matrix.zero_apply] at this
  exact hb this

theorem symplectic_oddCoreIn_eq_bot [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {A : GL (Fin n) K} (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = -(A : Matrix (Fin n) (Fin n) K)) :
    oddCoreIn B (conjAut n K A * dualAut n K) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  set R := A⁻¹ with hRdef
  have hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K) :=
    inv_transpose_of_transpose_eq_neg A hA
  have hn4 : 4 ≤ n := by
    have hev := CatalogueBAlternatingIsometry.even_finrank _
      (CatalogueBLinearHigherB.matrixForm_isAlt hK R hR)
      (CatalogueBLinearHigherB.matrixForm_nondegenerate R)
    rw [Module.finrank_fin_fun] at hev
    obtain ⟨k, hk⟩ := hev
    omega
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := exists_semilinear_of_odd hn hodd
  have hq := isQuasisimple_isometrySL_alt hK hn4 hinj hR
  have hfix : ∀ g ∈ isometrySL n R,
      (conjAut n K D * fieldAut n K τ) (proj n K g) = proj n K g :=
    fun g hg => commute_oddCoreIn_of_fixed hinj hB (graphLift A) (conjAut_mul_dualAut_proj A)
      (fun g hg => (graphLift_eq_iff A g).2 hg) (fun _ hh _ hg => conj_mem_isometrySL A hh hg)
      hq hy hg
  have hv : ∀ v : Fin n → K, v ≠ 0 → τ = 1 ∧ ∃ μ : K, (D : Matrix (Fin n) (Fin n) K) *ᵥ v =
      μ • v := by
    intro v hv
    obtain ⟨b, hb⟩ := exists_vecMul_ne_zero R hv
    obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have hN := vecMulVec_mul_self (vecMul_dotProduct_self_of_alt hK hR v)
    obtain ⟨hτ, hD⟩ := fix_unipotent_family (p := p) hN (a := a) (b := b)
      (by rw [vecMulVec_apply]; exact mul_ne_zero ha hb)
      (fun c => unipSL (vecMul_dotProduct_self_of_alt hK hR v) c) (fun c => rfl)
      (fun c => hfix _ (symTransv_mem hK hR v c))
    exact ⟨hτ, exists_eigen_of_commute_vecMulVec hb hD⟩
  have h0 : (Pi.single ⟨0, by omega⟩ 1 : Fin n → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  have hτ := (hv _ h0).1
  have hD : conjAut n K D = 1 := by
    refine conjAut_eq_one_of_eq_scalar ⟨0, by omega⟩ (eq_scalar_of_eigen _ fun v => ?_)
    by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0, mulVec_zero, smul_zero]⟩
    · exact (hv v hv0).2
  rw [hD, hτ, map_one, one_mul]

end CFSG.ComponentClassification.Burgoyne.PSL
