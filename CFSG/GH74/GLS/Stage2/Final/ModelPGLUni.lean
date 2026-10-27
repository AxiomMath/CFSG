module

public import CFSG.LieType.SteinbergBRUnitaryPlaneQuotient
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphField
public import CFSG.GH74.GLS.Stage2.Final.ModelPGLGen

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueBUnitaryTwo
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [CharP F p] in
theorem exists_norm_one_sq (hF : Nat.card F = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1) {δ : Fˣ}
    (hδ : δ ^ (p ^ f + 1) = 1) :
    ∃ c : Fˣ, c ^ (p ^ f + 1) = 1 ∧ (c * c * δ = 1 ∨ c * c * δ = -1) := by
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = 4 * m + 1 := ⟨p ^ f / 4, by omega⟩
  have key : ∀ δ : Fˣ, δ ^ (p ^ f + 1) = 1 → δ ^ (2 * m + 1) = 1 →
      ∃ c : Fˣ, c ^ (p ^ f + 1) = 1 ∧ c * c * δ = 1 := by
    intro δ hδ hδ'
    obtain ⟨u, hu⟩ := exists_pow_pred_eq hF (hq_one p f) hδ
    have hu' : u ^ (4 * m) = δ := by
      rw [← hu, hm]
      simp
    have e1 : (u ^ (2 * m)) ^ (p ^ f + 1) = 1 := by
      rw [← pow_mul, hm, show 2 * m * (4 * m + 1 + 1) = 4 * m * (2 * m + 1) by ring, pow_mul, hu']
      exact hδ'
    have e2 : u ^ (2 * m) * u ^ (2 * m) = δ := by
      rw [← pow_add, show 2 * m + 2 * m = 4 * m by ring]
      exact hu'
    refine ⟨(u ^ (2 * m))⁻¹, by rw [inv_pow, e1, inv_one], ?_⟩
    rw [← mul_inv, e2, inv_mul_cancel]
  have hy : δ ^ (2 * m + 1) * δ ^ (2 * m + 1) = 1 := by
    rw [← pow_add, show 2 * m + 1 + (2 * m + 1) = p ^ f + 1 by omega]
    exact hδ
  rcases units_sq_eq_one hy with h1 | h1
  · obtain ⟨c, hc, hcδ⟩ := key δ hδ h1
    exact ⟨c, hc, Or.inl hcδ⟩
  · have hev : Even (p ^ f + 1) := ⟨2 * m + 1, by omega⟩
    have hod : Odd (2 * m + 1) := ⟨m, rfl⟩
    have h2 : (-δ) ^ (p ^ f + 1) = 1 := by rw [hev.neg_pow]; exact hδ
    have h3 : (-δ) ^ (2 * m + 1) = 1 := by rw [hod.neg_pow, h1, neg_neg]
    obtain ⟨c, hc, hcδ⟩ := key (-δ) h2 h3
    refine ⟨c, hc, Or.inr ?_⟩
    rw [mul_neg] at hcδ
    exact neg_eq_iff_eq_neg.1 hcδ

omit [Finite F] in
theorem stdH_separatingRight (τ : F →+* F) :
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian (n := 2) τ).SeparatingRight := by
  intro y hy
  funext j
  have h1 := hy (Pi.single j 1)
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian_apply,
    Finset.sum_eq_single j] at h1
  · simpa using h1
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

omit [Finite F] in
theorem stdH_basis (τ : F →+* F) (i j : Fin 2) :
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian (n := 2) τ
      (Pi.basisFun F (Fin 2) i) (Pi.basisFun F (Fin 2) j) = if i = j then 1 else 0 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian_apply, Finset.sum_eq_single i]
  · simp only [Pi.basisFun_apply, Pi.single_eq_same, map_one, one_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp only [hij, ite_false]
      exact Pi.single_eq_of_ne hij _
  · intro k _ hk
    simp [Pi.basisFun_apply, Pi.single_eq_of_ne hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [Finite F] in
theorem sc2_mulVec (c : Fˣ) (v : Fin 2 → F) :
    ((sc2 c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = (c : F) • v := by
  ext i
  simp [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]

omit [Finite F] in
theorem eq_sc2_of_mulVec (A : GL (Fin 2) F) (c : Fˣ)
    (h : ∀ v : Fin 2 → F, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v = (c : F) • v) : A = sc2 c := by
  apply Units.ext
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  have h2 : ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pi.single j 1 : Fin 2 → F)) i =
      (A : Matrix (Fin 2) (Fin 2) F) i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h2] at h1
  rw [h1]
  fin_cases i <;> fin_cases j <;>
    simp [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem uni_psi (hF : Nat.card F = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1)
    (hC : ClsFacts (ModelData.uni hF)) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (Ψ : ↥(Hpm (ModelData.uni hF)) →* PGL2 F₀),
      Nat.card F₀ = p ^ f ∧ Function.Surjective Ψ ∧
        ∀ g : ↥(Hpm (ModelData.uni hF)), Ψ g = 1 ↔
          (g : GL (Fin 2) F) = 1 ∨ (g : GL (Fin 2) F) = -1 := by
  set σ' := unitaryFieldConjugation p f hF with hσ'
  have hσeq : σ' = unitaryInvolution F p f :=
    RingEquiv.ext fun x => by rw [hσ', unitaryFieldConjugation_apply, unitaryInvolution_apply]
  obtain ⟨-, -, hcard⟩ := unitaryFieldConjugation_data p f hF
  have hinv : ∀ x, σ' (σ' x) = x := fun x => by
    rw [hσeq]
    exact unitaryInvolution_involutive hF x
  let h := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian (n := 2) σ'.toRingHom
  have hsym : h.IsSymm :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian_isSymm (τ := σ'.toRingHom) hinv
  have hnd : h.Nondegenerate :=
    ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian_separatingLeft _,
      stdH_separatingRight _⟩
  have hdim : Module.finrank F (Fin 2 → F) = 2 := by simp
  obtain ⟨θ, hsurj, hker, -⟩ :=
    CFSG.LieType.odd_unitary_plane_full_projective_linear_quotient p f hF h hsym hnd hdim
  have hb : ∀ i j, h (Pi.basisFun F (Fin 2) i) (Pi.basisFun F (Fin 2) j) =
      if i = j then 1 else 0 := stdH_basis _
  let iso := isometryMatrixEquiv h (Pi.basisFun F (Fin 2)) hb
  have hle : Hpm (ModelData.uni hF) ≤ Uid σ' 2 := fun g hg =>
    (mem_Uid_iff σ' 2 g).2 (by rw [hσeq]; exact (mem_uniGL _).1 hg.1)
  have hU0 : ∀ X : GL (Fin 2) F, conjTr σ' (X : Matrix (Fin 2) (Fin 2) F) *
      (X : Matrix (Fin 2) (Fin 2) F) = 1 → X ∈ (ModelData.uni hF).U2 := fun X hX => by
    rw [hσeq] at hX
    exact (mem_uniGL _).2 hX
  have hU : ∀ A : ↥(Uid σ' 2), (A.val : GL (Fin 2) F) ∈ (ModelData.uni hF).U2 := fun A =>
    hU0 A.val ((mem_Uid_iff σ' 2 A.val).1 A.2)
  let Ψ₀ : ↥(Uid σ' 2) →* PGL2 ↥(CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ') :=
    θ.comp iso.symm.toMonoidHom
  let Ψ : ↥(Hpm (ModelData.uni hF)) →*
      PGL2 ↥(CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ') :=
    Ψ₀.comp (Subgroup.inclusion hle)
  have hsymm_apply : ∀ (A : ↥(Uid σ' 2)) (v : Fin 2 → F),
      ((iso.symm A : ↥(CFSG.ComponentClassification.CatalogueBUnitaryIsometry.isometryGroup h)) :
        (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) v = (A.val : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
    intro A v
    have h1 := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec
      (Pi.basisFun F (Fin 2)) ((iso.symm A).val) v
    have h2 : CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
        (Pi.basisFun F (Fin 2)) ((iso.symm A).val) = A.val := by
      have := isometryMatrixEquiv_val h (Pi.basisFun F (Fin 2)) hb (iso.symm A)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h2] at h1
    simpa using h1.symm
  have hK : ∀ A : ↥(Uid σ' 2), Ψ₀ A = 1 ↔
      ∃ c : Fˣ, (c : F) * σ' c = 1 ∧ (A.val : GL (Fin 2) F) = sc2 c := by
    intro A
    show θ (iso.symm A) = 1 ↔ _
    rw [hker]
    constructor
    · rintro ⟨c, hc, hv⟩
      refine ⟨c, hc, eq_sc2_of_mulVec _ c fun v => ?_⟩
      rw [← hsymm_apply]
      exact hv v
    · rintro ⟨c, hc, hA⟩
      refine ⟨c, hc, fun v => ?_⟩
      rw [hsymm_apply, hA, sc2_mulVec]
  refine ⟨_, inferInstance, inferInstance, Ψ, hcard, ?_, ?_⟩
  · intro x
    obtain ⟨g', rfl⟩ := hsurj x
    set A : ↥(Uid σ' 2) := iso g' with hAdef
    have hA : (A.val : GL (Fin 2) F) ∈ (ModelData.uni hF).U2 := hU A
    have hnorm := norm_det_uni (σ := unitaryInvolution F p f) hA
    set δ : Fˣ := Matrix.GeneralLinearGroup.det A.val with hδdef
    have hδF : (δ : F) = ((A.val : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det :=
      Matrix.GeneralLinearGroup.val_det_apply _
    have hδ : δ ^ (p ^ f + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one, hδF]
      rw [unitaryInvolution_apply] at hnorm
      exact hnorm
    obtain ⟨c, hc, hcδ⟩ := exists_norm_one_sq hF hq4 hδ
    have hcU : sc2 c ∈ (ModelData.uni hF).U2 := (sc2_mem_uni_iff hF c).2 hc
    have hcn : (c : F) * σ' c = 1 := by
      rw [hσeq, unitaryInvolution_apply, ← pow_succ']
      have := congrArg (fun v : Fˣ => (v : F)) hc
      simpa using this
    have hscUid : (sc2 c : GL (Fin 2) F) ∈ Uid σ' 2 :=
      (mem_Uid_iff σ' 2 _).2 (by rw [hσeq]; exact (mem_uniGL _).1 hcU)
    have hdetg : ((sc2 c * A.val : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 ∨
        ((sc2 c * A.val : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = -1 := by
      rw [Units.val_mul, Matrix.det_mul, det_sc2, ← hδF]
      rcases hcδ with h1 | h1
      · left
        have := congrArg (fun v : Fˣ => (v : F)) h1
        simp only [Units.val_mul, Units.val_one] at this
        rw [sq]; exact this
      · right
        have := congrArg (fun v : Fˣ => (v : F)) h1
        simp only [Units.val_mul, Units.val_neg, Units.val_one] at this
        rw [sq]; exact this
    refine ⟨⟨sc2 c * A.val, (ModelData.uni hF).U2.mul_mem hcU hA, hdetg⟩, ?_⟩
    have hprod : Subgroup.inclusion hle ⟨sc2 c * A.val, (ModelData.uni hF).U2.mul_mem hcU hA, hdetg⟩ =
        (⟨sc2 c, hscUid⟩ : ↥(Uid σ' 2)) * A := rfl
    show Ψ₀ (Subgroup.inclusion hle _) = θ g'
    rw [hprod, map_mul, (hK ⟨sc2 c, hscUid⟩).2 ⟨c, hcn, rfl⟩, one_mul]
    show θ (iso.symm A) = θ g'
    rw [hAdef, MulEquiv.symm_apply_apply]
  · intro g
    show Ψ₀ (Subgroup.inclusion hle g) = 1 ↔ _
    rw [hK]
    constructor
    · rintro ⟨c, hcn, hgc⟩
      have hgc' : (g : GL (Fin 2) F) = sc2 c := hgc
      have hU2 : sc2 c ∈ (ModelData.uni hF).U2 := hgc' ▸ g.2.1
      rcases g.2.2 with h1 | h1
      · have hu : c * c = 1 := by
          rw [hgc', det_sc2] at h1
          apply Units.ext
          simpa [sq] using h1
        rcases units_sq_eq_one hu with rfl | rfl
        · left; rw [hgc', sc2_one]
        · right; rw [hgc', sc2_neg_one]
      · exfalso
        have hu : c * c = -1 := by
          rw [hgc', det_sc2] at h1
          apply Units.ext
          simpa [sq] using h1
        exact hC.no_scalar_i c hU2 hu
    · rintro (h1 | h1)
      · refine ⟨1, ?_, ?_⟩
        · simp
        · show (g : GL (Fin 2) F) = _
          rw [h1, sc2_one]
      · refine ⟨-1, ?_, ?_⟩
        · simp
        · show (g : GL (Fin 2) F) = _
          rw [h1, sc2_neg_one]

theorem pglStmt_uni (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 1) :
    PglStmt (ModelData.uni hF) (p ^ f) (dP _ (dRefl F) dRefl_mem_uni) :=
  pglStmt_of_surj dRefl_mem_uni (uni_psi hF hq4 (clsFacts_uni hF hp2 h5 hq4))

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
