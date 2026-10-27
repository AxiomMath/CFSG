module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaNormal

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv fixedInnerEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv reindexMatrixEquiv reindexMatrixEquiv_mulVec reindexQuadraticForm_apply)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv statedDerivedReindexEquiv_val)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {d : ℕ}

section Proj

variable (eI : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)

theorem matrixProjectiveProjection_injective {Q' : QuadraticForm K (Fin d → K)}
    (h : matrixDerivedScalars Q' = ⊥) : Function.Injective (matrixProjectiveProjection Q') := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : x ∈ (matrixProjectiveProjection Q').ker := hx
  rw [matrixProjectiveProjection, QuotientGroup.ker_mk', h] at hx'
  exact hx'

@[expose] noncomputable def omegaProjEquiv
    (h : matrixDerivedScalars (reindexQuadraticForm eI Q) = ⊥) :
    StatedOmega Q0 ≃* matrixProjectiveDerived (reindexQuadraticForm eI Q) :=
  MulEquiv.ofBijective ((matrixProjectiveProjection (reindexQuadraticForm eI Q)).comp
      (statedDerivedReindexEquiv eI Q hQ).toMonoidHom)
    ⟨(matrixProjectiveProjection_injective h).comp (statedDerivedReindexEquiv eI Q hQ).injective,
      (matrixProjectiveProjection_surjective _).comp (statedDerivedReindexEquiv eI Q hQ).surjective⟩

theorem omegaProjEquiv_apply (h : matrixDerivedScalars (reindexQuadraticForm eI Q) = ⊥)
    (A : StatedOmega Q0) :
    omegaProjEquiv eI Q hQ h A =
      matrixProjectiveProjection _ (statedDerivedReindexEquiv eI Q hQ A) := rfl

end Proj

section Symmetry

variable (eI : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
  (h : matrixDerivedScalars (reindexQuadraticForm eI Q) = ⊥) (v : ι → K)

@[expose] noncomputable def omegaSymmetryAut : MulAut (StatedOmega Q0) :=
  MulAut.congr (omegaProjEquiv eI Q hQ h).symm
    (symmetryAut (reindexQuadraticForm eI Q) (reindexVectorEquiv eI v))

theorem omegaProjEquiv_omegaSymmetryAut (A : StatedOmega Q0) :
    omegaProjEquiv eI Q hQ h (omegaSymmetryAut eI Q hQ h v A) =
      symmetryAut (reindexQuadraticForm eI Q) (reindexVectorEquiv eI v)
        (omegaProjEquiv eI Q hQ h A) := by
  change omegaProjEquiv eI Q hQ h ((omegaProjEquiv eI Q hQ h).symm
    (symmetryAut (reindexQuadraticForm eI Q) (reindexVectorEquiv eI v)
      (omegaProjEquiv eI Q hQ h A))) = _
  rw [MulEquiv.apply_symm_apply]

theorem congr_omegaSymmetryAut :
    MulAut.congr (omegaProjEquiv eI Q hQ h) (omegaSymmetryAut eI Q hQ h v) =
      symmetryAut (reindexQuadraticForm eI Q) (reindexVectorEquiv eI v) := by
  ext x
  change omegaProjEquiv eI Q hQ h (omegaSymmetryAut eI Q hQ h v
    ((omegaProjEquiv eI Q hQ h).symm x)) = _
  rw [omegaProjEquiv_omegaSymmetryAut, MulEquiv.apply_symm_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem reindexQuadraticForm_reindexVectorEquiv (w : ι → K) :
    reindexQuadraticForm eI Q (reindexVectorEquiv eI w) = Q w := by
  rw [reindexQuadraticForm_apply]
  congr 1
  funext i
  rw [CatalogueBOrthogonalPointData.reindexVectorEquiv_apply, Equiv.symm_apply_apply]

theorem statedDerivedReindexEquiv_mulVec (A : StatedOmega Q0) (w : ι → K) :
    (((statedDerivedReindexEquiv eI Q hQ A : matrixDerived (reindexQuadraticForm eI Q)) :
        GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ reindexVectorEquiv eI w =
      reindexVectorEquiv eI (((A : GL ι K) : Matrix ι ι K) *ᵥ w) := by
  rw [← reindexMatrixEquiv_mulVec, ← statedDerivedReindexEquiv_val eI Q hQ]
  rfl

variable [CharP K 2]

theorem mem_fixedSubgroup_omegaSymmetryAut_iff
    (hQ' : (reindexQuadraticForm eI Q).polarBilin.Nondegenerate) (hv : Q v = 1)
    (A : StatedOmega Q0) :
    A ∈ fixedSubgroup (omegaSymmetryAut eI Q hQ h v) ↔
      ((A : GL ι K) : Matrix ι ι K) *ᵥ v = v := by
  set Q' := reindexQuadraticForm eI Q
  set y := statedDerivedReindexEquiv eI Q hQ A with hy
  have hv' : Q' (reindexVectorEquiv eI v) = 1 := by
    rw [reindexQuadraticForm_reindexVectorEquiv, hv]
  have hyO : (y : GL (Fin d) K) ∈ matrixIsometries Q' := matrixDerived_le_isometries Q' y.2
  change omegaSymmetryAut eI Q hQ h v A = A ↔ _
  rw [← (omegaProjEquiv eI Q hQ h).injective.eq_iff, omegaProjEquiv_omegaSymmetryAut,
    omegaProjEquiv_apply]
  unfold symmetryAut
  change matrixProjectiveConjugation Q' _ (matrixProjectiveProjection Q' y) = _ ↔ _
  rw [matrixProjectiveConjugation_mk, (matrixProjectiveProjection_injective h).eq_iff,
    ← (reindexVectorEquiv (K := K) eI).injective.eq_iff, ← statedDerivedReindexEquiv_mulVec eI Q hQ,
    ← hy, ← mem_centralizer_symmetryGL_iff hQ' hv' hyO, mem_centralizer_singleton_iff,
    Subtype.ext_iff, matrixDerivedConjugation_val, matrixIsometryInclusion_val]
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, MulAut.one_apply]
  constructor
  · intro h1
    calc (y : GL (Fin d) K) * symmetryGL Q' (reindexVectorEquiv eI v) =
          symmetryGL Q' (reindexVectorEquiv eI v) * y *
            (symmetryGL Q' (reindexVectorEquiv eI v))⁻¹ *
              symmetryGL Q' (reindexVectorEquiv eI v) := by rw [h1]
      _ = _ := by group
  · intro h1
    rw [← h1, mul_inv_cancel_right]

end Symmetry

section NormalForm

theorem center_eq_bot_of_mulEquiv_of_eq_bot {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hH : center H = ⊥) : center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ center H := Subgroup.mem_center_iff.mpr fun z => by
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx y)]
  rw [hH, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  exact e.injective (hx'.trans (map_one e).symm)

theorem center_matrixProjectiveDerived_eq_bot [CharP K 2] {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    center (matrixProjectiveDerived Q) = ⊥ := by
  have hcinj :=
    UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived hQ hT hE
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  apply hcinj
  rw [map_one]
  ext y
  rw [MulAut.conj_apply, MulAut.one_apply, (mem_center_iff.mp hx y).symm, mul_inv_cancel_right]

theorem mulAut_congr_congr_symm_cancel {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (ψ : MulAut H) :
    MulAut.congr e (MulAut.congr e.symm ψ) = ψ := by
  ext x
  simp [MulAut.congr_apply]

theorem congr_centerQuotientAut_of_center_eq_bot {G : Type*} [Group G] (hZ : center G = ⊥)
    (β : MulAut G) :
    MulAut.congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      (centerQuotientAut β) = β := by
  ext x
  set E := (QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot (G := G))
  have h1 : E.symm x = QuotientGroup.mk' (center G) x := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change E (centerQuotientAut β (E.symm x)) = β x
  rw [h1, centerQuotientAut_mk]
  rfl

variable [Finite K] [CharP K 2]

theorem exists_conj_omegaSymmetryAut {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (eI : ι ≃ Fin (2 * n)) (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K}
    (hQ : ⇑Q = Q0) (hQ' : (reindexQuadraticForm eI Q).polarBilin.Nondegenerate)
    (hT' : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, reindexQuadraticForm eI Q x = 0)
    (hE' : ⁅TauCeti.QuadraticMap.orthogonalGroup (reindexQuadraticForm eI Q),
      TauCeti.QuadraticMap.orthogonalGroup (reindexQuadraticForm eI Q)⁆ =
        elementaryGroup (reindexQuadraticForm eI Q))
    (hconj : ∀ α : MulAut (matrixProjectiveDerived (reindexQuadraticForm eI Q)), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage (reindexQuadraticForm eI Q))
    (h : matrixDerivedScalars (reindexQuadraticForm eI Q) = ⊥) {v : ι → K} (hv : Q v = 1)
    (β : MulAut (StatedOmega Q0)) (hβ2 : centerQuotientAut β * centerQuotientAut β = 1)
    (hβo : centerQuotientAut β ∉
      (MulAut.conj : StatedOmega Q0 ⧸ center (StatedOmega Q0) →* MulAut _).range)
    {f' : ℕ} (hfix : LieModel (fixedSubgroup (centerQuotientAut β)) .PSp 3 2 f') :
    ∃ Ψ : StatedOmega Q0 ≃* StatedOmega Q0, ∀ g, β (Ψ g) = Ψ (omegaSymmetryAut eI Q hQ h v g) := by
  set θ := omegaProjEquiv eI Q hQ h with hθ
  have hZ : center (StatedOmega Q0) = ⊥ :=
    center_eq_bot_of_mulEquiv_of_eq_bot θ (center_matrixProjectiveDerived_eq_bot hQ' hT' hE')
  have hE1 := congr_centerQuotientAut_of_center_eq_bot hZ β
  set E := (QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot (G := StatedOmega Q0)) with hEdef
  have hββ : β * β = 1 := by rw [← hE1, ← map_mul, hβ2, map_one]
  set α := MulAut.congr θ β with hαdef
  have hα2 : α * α = 1 := by rw [hαdef, ← map_mul, hββ, map_one]
  have hαo : α ∉ inner (matrixProjectiveDerived (reindexQuadraticForm eI Q)) := by
    rw [hαdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff, ← hE1,
      LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hβo
  have hβfix : LieModel (fixedSubgroup β) .PSp 3 2 f' := by
    have h1 := LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv E _) hfix
    rwa [hE1] at h1
  have hαfix : LieModel (fixedSubgroup α) .PSp 3 2 f' :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv θ β) hβfix
  have hv' : reindexQuadraticForm eI Q (reindexVectorEquiv eI v) = 1 := by
    rw [reindexQuadraticForm_reindexVectorEquiv, hv]
  obtain ⟨Ψ', hΨ'⟩ :=
    exists_conj_eq_symmetryAut hf hK hn hQ' hT' hE' hconj hv' α hα2 hαo hαfix
  refine ⟨MulAut.congr θ.symm Ψ', fun g => ?_⟩
  have key : β * MulAut.congr θ.symm Ψ' =
      MulAut.congr θ.symm Ψ' * omegaSymmetryAut eI Q hQ h v := by
    apply (MulAut.congr θ).injective
    rw [map_mul, map_mul, mulAut_congr_congr_symm_cancel, ← hαdef, congr_omegaSymmetryAut, hΨ']
    group
  exact congrArg (fun φ : MulAut (StatedOmega Q0) => φ g) key

theorem symmetryAut_not_mem_inner_of_regular {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {v : Fin d → K} (hv : Q v = 1) :
    symmetryAut Q v ∉ inner (matrixProjectiveDerived Q) := by
  rintro ⟨y, hy⟩
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q y
  rw [← kappa_derived_eq_conj] at hy
  have h1 := isometryKappa_injective hQ hT hE (a₁ := Subgroup.inclusion
    (matrixDerived_le_isometries Q) g) (a₂ := symmetryIsometry Q v) hy
  apply EvenOrthSelector.symmetryGL_not_mem_matrixDerived hQ hT hE hv
  have h2 : ((Subgroup.inclusion (matrixDerived_le_isometries Q) g : matrixIsometries Q) :
      GL (Fin d) K) = symmetryGL Q v := congrArg Subtype.val h1
  rw [← h2]
  exact g.2

theorem nonempty_fixedSubgroup_omegaSymmetryAut_mulEquiv {f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (eI : ι ≃ Fin (2 * n)) (Q : QuadraticForm K (ι → K))
    {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (hQ' : (reindexQuadraticForm eI Q).polarBilin.Nondegenerate)
    (hT' : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, reindexQuadraticForm eI Q x = 0)
    (hE' : ⁅TauCeti.QuadraticMap.orthogonalGroup (reindexQuadraticForm eI Q),
      TauCeti.QuadraticMap.orthogonalGroup (reindexQuadraticForm eI Q)⁆ =
        elementaryGroup (reindexQuadraticForm eI Q))
    (h : matrixDerivedScalars (reindexQuadraticForm eI Q) = ⊥) {v : ι → K} (hv : Q v = 1) :
    Nonempty (fixedSubgroup (omegaSymmetryAut eI Q hQ h v) ≃* StatedSp (n - 1) K) := by
  have hv' : reindexQuadraticForm eI Q (reindexVectorEquiv eI v) = 1 := by
    rw [reindexQuadraticForm_reindexVectorEquiv, hv]
  obtain ⟨e⟩ := omega_symmetry_fixed hf hK hn hQ' hT' hE' hv'
    (symmetryAut_not_mem_inner_of_regular hQ' hT' hE' hv')
  exact ⟨((fixedSubgroupCongrEquiv (omegaProjEquiv eI Q hQ h) _).trans (MulEquiv.subgroupCongr
    (congrArg fixedSubgroup (congr_omegaSymmetryAut eI Q hQ h v)))).trans e⟩

end NormalForm

end CFSG.SeitzReduction.F4Pilot
