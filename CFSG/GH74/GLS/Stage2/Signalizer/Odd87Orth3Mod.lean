module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonal CFSG.ComponentClassification.Burgoyne.PSL
open scoped MatrixGroups

section Adjoint

variable {k : Type} [Field k]

@[expose] def adMat (S : SL(2, k)) : Matrix (Fin 3) (Fin 3) k :=
  !![(S : Matrix (Fin 2) (Fin 2) k) 0 0 * (S : Matrix (Fin 2) (Fin 2) k) 1 1 +
        (S : Matrix (Fin 2) (Fin 2) k) 0 1 * (S : Matrix (Fin 2) (Fin 2) k) 1 0,
      -((S : Matrix (Fin 2) (Fin 2) k) 0 0 * (S : Matrix (Fin 2) (Fin 2) k) 1 0),
      (S : Matrix (Fin 2) (Fin 2) k) 0 1 * (S : Matrix (Fin 2) (Fin 2) k) 1 1;
    -(2 * (S : Matrix (Fin 2) (Fin 2) k) 0 0 * (S : Matrix (Fin 2) (Fin 2) k) 0 1),
      (S : Matrix (Fin 2) (Fin 2) k) 0 0 ^ 2, -((S : Matrix (Fin 2) (Fin 2) k) 0 1 ^ 2);
    2 * (S : Matrix (Fin 2) (Fin 2) k) 1 0 * (S : Matrix (Fin 2) (Fin 2) k) 1 1,
      -((S : Matrix (Fin 2) (Fin 2) k) 1 0 ^ 2), (S : Matrix (Fin 2) (Fin 2) k) 1 1 ^ 2]

theorem det_adMat (S : SL(2, k)) : (adMat S).det = 1 := by
  have hdet : (S : Matrix (Fin 2) (Fin 2) k) 0 0 * (S : Matrix (Fin 2) (Fin 2) k) 1 1 -
      (S : Matrix (Fin 2) (Fin 2) k) 0 1 * (S : Matrix (Fin 2) (Fin 2) k) 1 0 = 1 := by
    have := S.2
    rw [Matrix.det_fin_two] at this
    exact this
  have key : (adMat S).det = ((S : Matrix (Fin 2) (Fin 2) k) 0 0 * (S : Matrix (Fin 2) (Fin 2) k) 1 1 -
      (S : Matrix (Fin 2) (Fin 2) k) 0 1 * (S : Matrix (Fin 2) (Fin 2) k) 1 0) ^ 3 := by
    rw [Matrix.det_fin_three]
    simp [adMat]
    ring
  rw [key, hdet, one_pow]

theorem trace_adMat (S : SL(2, k)) :
    (adMat S).trace = ((S : Matrix (Fin 2) (Fin 2) k) 0 0 + (S : Matrix (Fin 2) (Fin 2) k) 1 1) ^ 2 - 1 := by
  have hdet : (S : Matrix (Fin 2) (Fin 2) k) 0 0 * (S : Matrix (Fin 2) (Fin 2) k) 1 1 -
      (S : Matrix (Fin 2) (Fin 2) k) 0 1 * (S : Matrix (Fin 2) (Fin 2) k) 1 0 = 1 := by
    have := S.2
    rw [Matrix.det_fin_two] at this
    exact this
  simp [Matrix.trace, Fin.sum_univ_three, adMat]
  linear_combination -hdet

theorem coord_ad (S : SL(2, k)) (x : Fin 3 → k) :
    (traceZeroCoordinates k).symm ((traceZeroOrthogonalAction (Matrix.SpecialLinearGroup.toGL S)).val
      (traceZeroCoordinates k x)) = adMat S *ᵥ x := by
  have hinv : (((Matrix.SpecialLinearGroup.toGL S)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(S : Matrix (Fin 2) (Fin 2) k) 1 1, -(S : Matrix (Fin 2) (Fin 2) k) 0 1;
        -(S : Matrix (Fin 2) (Fin 2) k) 1 0, (S : Matrix (Fin 2) (Fin 2) k) 0 0] := by
    have h1 : (Matrix.SpecialLinearGroup.toGL S)⁻¹ = Matrix.SpecialLinearGroup.toGL S⁻¹ := by
      rw [map_inv]
    rw [h1]
    have h2 : ((Matrix.SpecialLinearGroup.toGL S⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
        ((S⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) := rfl
    rw [h2, Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hS : ((Matrix.SpecialLinearGroup.toGL S : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (S : Matrix (Fin 2) (Fin 2) k) := by simp
  ext i
  have hv := traceZeroOrthogonalAction_val (Matrix.SpecialLinearGroup.toGL S) (traceZeroCoordinates k x)
  rw [hinv, hS, traceZeroCoordinates_val] at hv
  fin_cases i
  · show ((traceZeroOrthogonalAction (Matrix.SpecialLinearGroup.toGL S)).val
      (traceZeroCoordinates k x)).val 0 0 = _
    rw [hv]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, adMat, Matrix.mulVec, dotProduct]
    ring
  · show ((traceZeroOrthogonalAction (Matrix.SpecialLinearGroup.toGL S)).val
      (traceZeroCoordinates k x)).val 0 1 = _
    rw [hv]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, adMat, Matrix.mulVec, dotProduct]
    ring
  · show ((traceZeroOrthogonalAction (Matrix.SpecialLinearGroup.toGL S)).val
      (traceZeroCoordinates k x)).val 1 0 = _
    rw [hv]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, adMat, Matrix.mulVec, dotProduct]
    ring

@[expose] def uElt : SL(2, k) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def vElt : SL(2, k) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem adMat_uElt_mulVec (w : Fin 3 → k) :
    adMat (uElt : SL(2, k)) *ᵥ w = ![w 0 + w 2, -2 * w 0 + w 1 - w 2, w 2] := by
  ext i
  fin_cases i <;> simp [adMat, uElt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring

theorem adMat_vElt_mulVec (w : Fin 3 → k) :
    adMat (vElt : SL(2, k)) *ᵥ w = ![w 0 - w 1, w 1, 2 * w 0 - w 1 + w 2] := by
  ext i
  fin_cases i <;> simp [adMat, vElt, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

abbrev v3 (a b c : k) : Fin 3 → k := ![a, b, c]

omit [Field k] in
theorem v3_eq (w : Fin 3 → k) : w = v3 (w 0) (w 1) (w 2) := by
  ext i
  fin_cases i <;> rfl

theorem irreducible_uv (h2 : (2 : k) ≠ 0) (W : Submodule k (Fin 3 → k))
    (hU : ∀ w ∈ W, adMat (uElt : SL(2, k)) *ᵥ w ∈ W)
    (hV : ∀ w ∈ W, adMat (vElt : SL(2, k)) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hNU : ∀ w ∈ W, v3 (w 2) (-2 * w 0 - w 2) 0 ∈ W := by
    intro w hw
    have := W.sub_mem (hU w hw) hw
    rw [adMat_uElt_mulVec] at this
    convert this using 1
    ext i
    fin_cases i <;> simp; ring
  have hNV : ∀ w ∈ W, v3 (-w 1) 0 (2 * w 0 - w 1) ∈ W := by
    intro w hw
    have := W.sub_mem (hV w hw) hw
    rw [adMat_vElt_mulVec] at this
    convert this using 1
    ext i
    fin_cases i <;> simp
  have e1_of : ∀ w ∈ W, w 2 ≠ 0 → v3 (0 : k) 1 0 ∈ W := by
    intro w hw hw2
    have h1 := hNU _ (hNU w hw)
    have h3 := W.smul_mem ((-2 * w 2)⁻¹) h1
    have hne : (-2 * w 2) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2) hw2
    convert h3 using 1
    ext i
    fin_cases i <;> simp; field_simp
  have e2_of : ∀ w ∈ W, w 1 ≠ 0 → v3 (0 : k) 0 1 ∈ W := by
    intro w hw hw1
    have h1 := hNV _ (hNV w hw)
    have h3 := W.smul_mem ((-2 * w 1)⁻¹) h1
    have hne : (-2 * w 1) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2) hw1
    convert h3 using 1
    ext i
    fin_cases i <;> simp; field_simp
  have top_of_e1 : v3 (0 : k) 1 0 ∈ W → W = ⊤ := by
    intro he1
    have he2 : v3 (0 : k) 0 1 ∈ W := e2_of _ he1 (by simp)
    have h3 := hNV _ he1
    have he0 : v3 (1 : k) 0 0 ∈ W := by
      have h4 := W.add_mem h3 he2
      have h5 := W.smul_mem (-1 : k) h4
      convert h5 using 1
      ext i
      fin_cases i <;> simp
    rw [eq_top_iff]
    intro w _
    rw [v3_eq w]
    have : v3 (w 0) (w 1) (w 2) =
        w 0 • v3 (1 : k) 0 0 + w 1 • v3 (0 : k) 1 0 + w 2 • v3 (0 : k) 0 1 := by
      ext i
      fin_cases i <;> simp
    rw [this]
    exact W.add_mem (W.add_mem (W.smul_mem _ he0) (W.smul_mem _ he1)) (W.smul_mem _ he2)
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    by_cases h2w : w 2 ≠ 0
    · exact top_of_e1 (e1_of w hw h2w)
    · push Not at h2w
      by_cases h1w : w 1 ≠ 0
      · have he2 := e2_of w hw h1w
        exact top_of_e1 (e1_of _ he2 (by simp))
      · push Not at h1w
        have h0w : w 0 ≠ 0 := by
          intro h0
          apply hw0
          rw [v3_eq w, h0, h1w, h2w]
          ext i
          fin_cases i <;> simp
        have he0 : v3 (1 : k) 0 0 ∈ W := by
          have := W.smul_mem (w 0)⁻¹ hw
          convert this using 1
          rw [v3_eq w, h1w, h2w]
          ext i
          fin_cases i <;> simp [h0w]
        have h3 := hNU _ he0
        apply top_of_e1
        have h4 := W.smul_mem (-2 : k)⁻¹ h3
        convert h4 using 1
        ext i
        fin_cases i <;> simp [h2]

theorem commutant_uv (h2 : (2 : k) ≠ 0) (M : Matrix (Fin 3) (Fin 3) k)
    (hU : M * adMat (uElt : SL(2, k)) = adMat uElt * M) (hV : M * adMat (vElt : SL(2, k)) = adMat vElt * M) :
    ∃ c : k, M = c • (1 : Matrix (Fin 3) (Fin 3) k) := by
  have eU : ∀ i j, (M * adMat (uElt : SL(2, k))) i j = (adMat (uElt : SL(2, k)) * M) i j :=
    fun i j => by rw [hU]
  have eV : ∀ i j, (M * adMat (vElt : SL(2, k))) i j = (adMat (vElt : SL(2, k)) * M) i j :=
    fun i j => by rw [hV]
  have u00 := eU 0 0
  have u01 := eU 0 1
  have u02 := eU 0 2
  have u10 := eU 1 0
  have u22 := eU 2 2
  have v00 := eV 0 0
  have v01 := eV 0 1
  have v02 := eV 0 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, adMat, uElt, vElt] at u00 u01 u02 u10 u22 v00 v01 v02
  have h21 : M 2 1 = 0 := u01
  have h20 : M 2 0 = 0 := by linear_combination u22 + u01
  have h01 : M 0 1 = 0 := by
    have : 2 * M 0 1 = 0 := by linear_combination -u00 - h20
    exact (mul_eq_zero.mp this).resolve_left h2
  have h11 : M 1 1 = M 0 0 := by
    have : 2 * (M 1 1 - M 0 0) = 0 := by linear_combination -u10 + h20
    have := (mul_eq_zero.mp this).resolve_left h2
    linear_combination this
  have h22 : M 2 2 = M 0 0 := by linear_combination -u02 - h01
  have h02 : M 0 2 = 0 := by linear_combination -v01 + h11
  have h10 : M 1 0 = 0 := by linear_combination v00 - 2 * h02
  have h12 : M 1 2 = 0 := v02
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, h11, h22]

end Adjoint

section Transport

variable {k : Type} [Field k]

theorem isoOrthGL_mulVec (hk : ringChar k ≠ 2) (R : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R)
    (g : TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm R))
    (w : Fin 3 → k) :
    (((isoOrthGL hk R hR g : ↥(CatalogueBGraphForm.isometryGroup 3 k R)) : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) *ᵥ w = (g : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) w := by
  have h1 : (((isoOrthGL hk R hR g : ↥(CatalogueBGraphForm.isometryGroup 3 k R)) : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) =
      ((CatalogueBAlternatingIsometry.basisMatrixEquiv (Pi.basisFun k (Fin 3))
        (g : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := rfl
  rw [h1]
  have := CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec (Pi.basisFun k (Fin 3))
    (g : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) w
  simpa using this

@[expose] def omega3 (R : GL (Fin 3) k) : Subgroup SL(3, k) :=
  (⁅CatalogueBGraphForm.isometryGroup 3 k R, CatalogueBGraphForm.isometryGroup 3 k R⁆).comap
    Matrix.SpecialLinearGroup.toGL

theorem commutator_le_self_of_comm (I : Subgroup (GL (Fin 3) k)) : ⁅I, I⁆ ≤ I :=
  Subgroup.commutator_le.mpr fun _ hx _ hy =>
    I.mul_mem (I.mul_mem (I.mul_mem hx hy) (I.inv_mem hx)) (I.inv_mem hy)

theorem omega3_le_isometrySL (R : GL (Fin 3) k) :
    omega3 R ≤ (CatalogueBGraphForm.isometryGroup 3 k R).comap Matrix.SpecialLinearGroup.toGL :=
  fun _ hg => commutator_le_self_of_comm _ hg

variable [Finite k]

theorem two_ne_zero_of_odd_card (hodd : Odd (Nat.card k)) : (2 : k) ≠ 0 := by
  intro h2
  have hk : ringChar k = 2 := by
    have := CharP.ringChar_of_prime_eq_zero Nat.prime_two (by simpa using h2)
    exact this
  have : Fintype k := Fintype.ofFinite k
  have h1 := FiniteField.even_card_of_char_two hk
  rw [← Nat.card_eq_fintype_card] at h1
  obtain ⟨m, hm⟩ := hodd
  omega

theorem ad_param (hodd : Odd (Nat.card k)) (R : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) :
    ∃ (ι : SL(2, k) →* SL(3, k)) (P P' : Matrix (Fin 3) (Fin 3) k), P * P' = 1 ∧ P' * P = 1 ∧
      (∀ S : SL(2, k), ι S ∈ (CatalogueBGraphForm.isometryGroup 3 k R).comap
        Matrix.SpecialLinearGroup.toGL) ∧
      (∀ S : SL(2, k), (ι S : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P) ∧
      (Nat.card k ≠ 3 → ι.range = omega3 R) := by
  classical
  have hk : ringChar k ≠ 2 := by
    intro h
    have : Fintype k := Fintype.ofFinite k
    have h1 := FiniteField.even_card_of_char_two h
    rw [← Nat.card_eq_fintype_card] at h1
    obtain ⟨m, hm⟩ := hodd
    omega
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk R hR
  have hdim : Module.finrank k (Fin 3 → k) = 3 := Module.finrank_fin_fun k
  have key : ∃ (ψ : (Fin 3 → k) ≃ₗ[k] ↥(traceZeroSubmodule k))
      (e : ↥(TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm R)) ≃*
        ↥(TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm k))),
      (∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm R)))
        (X : ↥(traceZeroSubmodule k)),
        ((e g : ↥(TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm k))) :
          ↥(traceZeroSubmodule k) ≃ₗ[k] ↥(traceZeroSubmodule k)) X =
        ψ (((g : ↥(TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm R))) :
          (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) (ψ.symm X))) ∧
      (Nat.card k ≠ 3 → _root_.commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBLinearHigherB.matrixQuadraticForm R)) =
          Subgroup.map e.symm.toMonoidHom (traceZeroSpecialImage k)) := by
    by_cases hk3 : Nat.card k = 3
    · obtain ⟨d, ψ, e, -, he, -⟩ :=
        CatalogueBOrthogonalThreeSimilarity.exists_trace_zero_similarity_and_orthogonal_equiv hodd
          (CatalogueBLinearHigherB.matrixQuadraticForm R) hQnd hdim
      exact ⟨ψ, e, fun g X => by
        have := LinearEquiv.congr_fun (he g) X
        simpa using this, fun h => absurd hk3 h⟩
    · obtain ⟨d, ψ, e, -, he, hcomm, -, -⟩ := orthogonal_three_derived hodd hk3
        (CatalogueBLinearHigherB.matrixQuadraticForm R) hQnd hdim
      exact ⟨ψ, e, he, fun _ => hcomm⟩
  obtain ⟨ψ, e, he, hcomm⟩ := key
  set ε := isoOrthGL hk R hR with hε
  let ι₁ : SL(2, k) →* GL (Fin 3) k :=
    (CatalogueBGraphForm.isometryGroup 3 k R).subtype.comp
      (ε.toMonoidHom.comp (e.symm.toMonoidHom.comp
        (traceZeroOrthogonalAction.comp (Matrix.SpecialLinearGroup.toGL : SL(2, k) →* GL (Fin 2) k))))
  let ψ' : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k) := ψ.trans (traceZeroCoordinates k).symm
  have hact : ∀ (S : SL(2, k)) (w : Fin 3 → k),
      ((ι₁ S : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ w = ψ'.symm (adMat S *ᵥ ψ' w) := by
    intro S w
    have h1 : ((ι₁ S : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ w =
        ((e.symm (traceZeroOrthogonalAction (Matrix.SpecialLinearGroup.toGL S)) :
          TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm R)) :
          (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) w := isoOrthGL_mulVec hk R hR _ w
    rw [h1]
    set J := traceZeroOrthogonalAction (Matrix.SpecialLinearGroup.toGL S) with hJ
    have h2 := he (e.symm J) (ψ w)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h2
    have h3 : ((e.symm J : TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBLinearHigherB.matrixQuadraticForm R)) : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) w =
        ψ.symm ((J : (traceZeroSubmodule k) ≃ₗ[k] (traceZeroSubmodule k)) (ψ w)) := by
      rw [h2, LinearEquiv.symm_apply_apply]
    rw [h3]
    have h4 := coord_ad S ((traceZeroCoordinates k).symm (ψ w))
    rw [LinearEquiv.apply_symm_apply] at h4
    show _ = ψ.symm ((traceZeroCoordinates k) (adMat S *ᵥ (traceZeroCoordinates k).symm (ψ w)))
    rw [← h4, LinearEquiv.apply_symm_apply]
  set P : Matrix (Fin 3) (Fin 3) k := LinearMap.toMatrix' ψ'.toLinearMap with hP
  set P' : Matrix (Fin 3) (Fin 3) k := LinearMap.toMatrix' ψ'.symm.toLinearMap with hP'
  have hPP' : P * P' = 1 := by
    rw [hP, hP', ← LinearMap.toMatrix'_comp]
    have : ψ'.toLinearMap ∘ₗ ψ'.symm.toLinearMap = LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hP'P : P' * P = 1 := by
    rw [hP, hP', ← LinearMap.toMatrix'_comp]
    have : ψ'.symm.toLinearMap ∘ₗ ψ'.toLinearMap = LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hmat : ∀ S : SL(2, k), ((ι₁ S : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P := by
    intro S
    rw [Matrix.ext_iff_mulVec]
    intro w
    rw [hact S w, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP, hP', LinearMap.toMatrix'_mulVec,
      LinearMap.toMatrix'_mulVec]
    rfl
  have hdetι : ∀ S : SL(2, k), ((ι₁ S : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det = 1 := by
    intro S
    rw [hmat S, Matrix.det_mul, Matrix.det_mul, det_adMat, mul_one]
    have := congrArg Matrix.det hP'P
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact this
  let ι : SL(2, k) →* SL(3, k) :=
    { toFun := fun S => ⟨((ι₁ S : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k), hdetι S⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun S T => by
        apply Subtype.ext
        show ((ι₁ (S * T) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
          ((ι₁ S : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * ((ι₁ T : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
        rw [map_mul]
        rfl }
  have hιGL : ∀ S : SL(2, k), Matrix.SpecialLinearGroup.toGL (ι S) = ι₁ S := fun S => Units.ext rfl
  refine ⟨ι, P, P', hPP', hP'P, fun S => ?_, fun S => hmat S, fun hk3 => ?_⟩
  · rw [Subgroup.mem_comap, hιGL]
    exact (ε (e.symm (traceZeroOrthogonalAction (Matrix.SpecialLinearGroup.toGL S)))).2
  have hrange : (ι₁.range : Subgroup (GL (Fin 3) k)) =
      ⁅CatalogueBGraphForm.isometryGroup 3 k R, CatalogueBGraphForm.isometryGroup 3 k R⁆ := by
    have h1 : ι₁.range = Subgroup.map (CatalogueBGraphForm.isometryGroup 3 k R).subtype
        (Subgroup.map ε.toMonoidHom (Subgroup.map e.symm.toMonoidHom (traceZeroSpecialImage k))) := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp]
      rfl
    rw [h1, ← hcomm hk3]
    exact trans_commutator ε
  ext g
  constructor
  · rintro ⟨S, rfl⟩
    unfold omega3
    rw [Subgroup.mem_comap, hιGL, ← hrange]
    exact ⟨S, rfl⟩
  · intro hg
    have hg' : Matrix.SpecialLinearGroup.toGL g ∈ ι₁.range := by
      rw [hrange]; exact (Subgroup.mem_comap.mp hg)
    obtain ⟨S, hS⟩ := hg'
    refine ⟨S, ?_⟩
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [hιGL, hS]

theorem omega3_param (hodd : Odd (Nat.card k)) (h5 : 5 ≤ Nat.card k) (R : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) :
    ∃ (ι : SL(2, k) →* SL(3, k)) (P P' : Matrix (Fin 3) (Fin 3) k), P * P' = 1 ∧ P' * P = 1 ∧
      ι.range = omega3 R ∧ ∀ S : SL(2, k), (ι S : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P := by
  obtain ⟨ι, P, P', h1, h2, -, h4, h5'⟩ := ad_param hodd R hR
  exact ⟨ι, P, P', h1, h2, h5' (by omega), h4⟩

section Param

variable {ι : SL(2, k) →* SL(3, k)} {P P' : Matrix (Fin 3) (Fin 3) k}

omit [Finite k] in
theorem irreducible_of_param (h2 : (2 : k) ≠ 0) (hPP' : P * P' = 1) (hP'P : P' * P = 1)
    (hι : ∀ S : SL(2, k), (ι S : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P)
    (W : Submodule k (Fin 3 → k))
    (hW : ∀ S : SL(2, k), ∀ v ∈ W, (ι S : Matrix (Fin 3) (Fin 3) k) *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let W' : Submodule k (Fin 3 → k) := W.comap (Matrix.mulVecLin P')
  have hW' : ∀ S : SL(2, k), ∀ x ∈ W', adMat S *ᵥ x ∈ W' := by
    intro S x hx
    show P' *ᵥ (adMat S *ᵥ x) ∈ W
    have hmatid : P' * adMat S = (ι S : Matrix (Fin 3) (Fin 3) k) * P' := by
      rw [hι S, Matrix.mul_assoc, Matrix.mul_assoc, hPP', Matrix.mul_one]
    have : P' *ᵥ (adMat S *ᵥ x) = (ι S : Matrix (Fin 3) (Fin 3) k) *ᵥ (P' *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmatid]
    rw [this]
    exact hW S _ hx
  rcases irreducible_uv h2 W' (fun w hw => hW' uElt w hw) (fun w hw => hW' vElt w hw) with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : P *ᵥ w ∈ W' := by
      show P' *ᵥ (P *ᵥ w) ∈ W
      rw [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec]
      exact hw
    rw [h] at h1
    have h3 : P *ᵥ w = 0 := (Submodule.mem_bot k).mp h1
    have h4 : w = P' *ᵥ (P *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec]
    rw [Submodule.mem_bot, h4, h3, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : P *ᵥ w ∈ W' := by rw [h]; exact Submodule.mem_top
    have h2' : P' *ᵥ (P *ᵥ w) ∈ W := h1
    rwa [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec] at h2'

omit [Finite k] in
theorem commutant_of_param (h2 : (2 : k) ≠ 0) (hPP' : P * P' = 1) (hP'P : P' * P = 1)
    (hι : ∀ S : SL(2, k), (ι S : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P)
    (T : Matrix (Fin 3) (Fin 3) k)
    (hT : ∀ S : SL(2, k), T * (ι S : Matrix (Fin 3) (Fin 3) k) = (ι S : Matrix (Fin 3) (Fin 3) k) * T) :
    ∃ c : k, T = c • (1 : Matrix (Fin 3) (Fin 3) k) := by
  have hadj : ∀ S : SL(2, k), adMat S = P * (ι S : Matrix (Fin 3) (Fin 3) k) * P' := by
    intro S
    rw [hι S]
    calc adMat S = (P * P') * adMat S * (P * P') := by rw [hPP', Matrix.one_mul, Matrix.mul_one]
      _ = P * (P' * adMat S * P) * P' := by simp only [Matrix.mul_assoc]
  have hcomm : ∀ S : SL(2, k), (P * T * P') * adMat S = adMat S * (P * T * P') := by
    intro S
    have h := hT S
    rw [hadj S]
    calc P * T * P' * (P * (ι S : Matrix (Fin 3) (Fin 3) k) * P')
        = P * T * (P' * P) * (ι S : Matrix (Fin 3) (Fin 3) k) * P' := by simp only [Matrix.mul_assoc]
      _ = P * (T * (ι S : Matrix (Fin 3) (Fin 3) k)) * P' := by
          rw [hP'P, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * ((ι S : Matrix (Fin 3) (Fin 3) k) * T) * P' := by rw [h]
      _ = P * (ι S : Matrix (Fin 3) (Fin 3) k) * P' * (P * T * P') := by
          calc P * ((ι S : Matrix (Fin 3) (Fin 3) k) * T) * P'
              = P * (ι S : Matrix (Fin 3) (Fin 3) k) * (P' * P) * T * P' := by
                rw [hP'P, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := commutant_uv h2 (P * T * P') (hcomm uElt) (hcomm vElt)
  refine ⟨c, ?_⟩
  calc T = P' * (P * T * P') * P := by
        calc T = (P' * P) * T * (P' * P) := by rw [hP'P, Matrix.one_mul, Matrix.mul_one]
          _ = P' * (P * T * P') * P := by simp only [Matrix.mul_assoc]
    _ = c • 1 := by
        rw [hc]
        simp [hP'P]

omit [Finite k] in
theorem ker_of_param (h2 : (2 : k) ≠ 0) (hPP' : P * P' = 1) (_hP'P : P' * P = 1)
    (hι : ∀ S : SL(2, k), (ι S : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P)
    (S : SL(2, k)) (hS : ι S = 1) : S = 1 ∨ S = -1 := by
  have h1 : adMat S = 1 := by
    have h3 : (ι S : Matrix (Fin 3) (Fin 3) k) = 1 := by rw [hS]; rfl
    rw [hι S] at h3
    calc adMat S = (P * P') * adMat S * (P * P') := by rw [hPP', Matrix.one_mul, Matrix.mul_one]
      _ = P * (P' * adMat S * P) * P' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h3, Matrix.mul_one, hPP']
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have e02 := congrFun (congrFun h1 0) 2
  have e10 := congrFun (congrFun h1 1) 0
  have e11 := congrFun (congrFun h1 1) 1
  have e12 := congrFun (congrFun h1 1) 2
  have e21 := congrFun (congrFun h1 2) 1
  have e22 := congrFun (congrFun h1 2) 2
  simp [adMat] at e00 e01 e02 e10 e11 e12 e21 e22
  have hdet := S.2
  rw [Matrix.det_fin_two] at hdet
  set a := (S : Matrix (Fin 2) (Fin 2) k) 0 0
  set b := (S : Matrix (Fin 2) (Fin 2) k) 0 1
  set c := (S : Matrix (Fin 2) (Fin 2) k) 1 0
  set d := (S : Matrix (Fin 2) (Fin 2) k) 1 1
  have hb : b = 0 := e12
  have hc : c = 0 := e21
  rw [hb, hc] at hdet e00
  have had : a * d = 1 := by linear_combination hdet
  rcases e11 with ha | ha <;> rcases e22 with hd | hd
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hd, hb, hc, a, b, c, d]
  · exfalso
    rw [ha, hd] at had
    apply h2
    linear_combination -had
  · exfalso
    rw [ha, hd] at had
    apply h2
    linear_combination -had
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hd, hb, hc, a, b, c, d]

end Param

theorem exists_ad_hom3 (hodd : Odd (Nat.card k)) (R : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) :
    ∃ ι : SL(2, k) →* SL(3, k),
      (∀ S, ι S ∈ (CatalogueBGraphForm.isometryGroup 3 k R).comap Matrix.SpecialLinearGroup.toGL) ∧
      (∀ W : Submodule k (Fin 3 → k), (∀ S : SL(2, k), ∀ v ∈ W, (ι S : Matrix (Fin 3) (Fin 3) k) *ᵥ v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      (∀ T : Matrix (Fin 3) (Fin 3) k,
        (∀ S : SL(2, k), T * (ι S : Matrix (Fin 3) (Fin 3) k) = (ι S : Matrix (Fin 3) (Fin 3) k) * T) →
        ∃ c : k, T = c • (1 : Matrix (Fin 3) (Fin 3) k)) ∧
      (∀ S, ι S = 1 → S = 1 ∨ S = -1) := by
  obtain ⟨ι, P, P', hPP', hP'P, hiso, hι, -⟩ := ad_param hodd R hR
  have h2 := two_ne_zero_of_odd_card hodd
  exact ⟨ι, hiso, fun W hW => irreducible_of_param h2 hPP' hP'P hι W hW,
    fun T hT => commutant_of_param h2 hPP' hP'P hι T hT,
    fun S hS => ker_of_param h2 hPP' hP'P hι S hS⟩

theorem exists_sl2_hom (hodd : Odd (Nat.card k)) (h5 : 5 ≤ Nat.card k) (R : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) : ∃ ι : SL(2, k) →* SL(3, k), ι.range = omega3 R := by
  obtain ⟨ι, -, -, -, -, hrange, -⟩ := omega3_param hodd h5 R hR
  exact ⟨ι, hrange⟩

theorem omega3_perfect (hodd : Odd (Nat.card k)) (h5 : 5 ≤ Nat.card k) (R : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) : Group.IsPerfect (omega3 R) := by
  obtain ⟨ι, -, -, -, -, hrange, -⟩ := omega3_param hodd h5 R hR
  have hq := CatalogueBGeneralLinear.specialLinear_quasisimple 2 k le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))
  have : Group.IsPerfect SL(2, k) := hq.1
  have : Group.IsPerfect ↥ι.range :=
    Group.IsPerfect.ofSurjective (f := ι.rangeRestrict) ι.rangeRestrict_surjective
  rw [← hrange]
  exact this

theorem omega3_irreducible (hodd : Odd (Nat.card k)) (h5 : 5 ≤ Nat.card k) (R : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) (W : Submodule k (Fin 3 → k))
    (hW : ∀ g ∈ omega3 R, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) k) *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨ι, P, P', hPP', hP'P, hrange, hι⟩ := omega3_param hodd h5 R hR
  refine irreducible_of_param (two_ne_zero_of_odd_card hodd) hPP' hP'P hι W fun S v hv => ?_
  exact hW _ (hrange ▸ MonoidHom.mem_range.mpr ⟨S, rfl⟩) v hv

theorem omega3_commutant (hodd : Odd (Nat.card k)) (h5 : 5 ≤ Nat.card k) (R : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) (T : Matrix (Fin 3) (Fin 3) k)
    (hT : ∀ g ∈ omega3 R, T * (g : Matrix (Fin 3) (Fin 3) k) = (g : Matrix (Fin 3) (Fin 3) k) * T) :
    ∃ c : k, T = c • (1 : Matrix (Fin 3) (Fin 3) k) := by
  obtain ⟨ι, P, P', hPP', hP'P, hrange, hι⟩ := omega3_param hodd h5 R hR
  refine commutant_of_param (two_ne_zero_of_odd_card hodd) hPP' hP'P hι T fun S => ?_
  exact hT _ (hrange ▸ MonoidHom.mem_range.mpr ⟨S, rfl⟩)

theorem omega3_trace_exists (hodd : Odd (Nat.card k)) (h5 : 5 ≤ Nat.card k) (R : GL (Fin 3) k)
    (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) (t : k) :
    ∃ g ∈ omega3 R, Matrix.trace (g : Matrix (Fin 3) (Fin 3) k) = t ^ 2 - 1 := by
  obtain ⟨ι, P, P', hPP', hP'P, hrange, hι⟩ := omega3_param hodd h5 R hR
  let S : SL(2, k) := ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  refine ⟨ι S, hrange ▸ MonoidHom.mem_range.mpr ⟨S, rfl⟩, ?_⟩
  rw [hι S, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hPP', Matrix.mul_one,
    trace_adMat S]
  simp [S]

end Transport

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
