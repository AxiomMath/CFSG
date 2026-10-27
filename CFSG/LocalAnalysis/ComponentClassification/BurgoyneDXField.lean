module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCoordinateEquiv)

section FieldMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K K' : Type} [Field K] [Field K'] (φ : K ≃+* K')

@[expose] def glMapEquiv : GL ι K ≃* GL ι K' :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := ι) φ).toMulEquiv

theorem coe_glMapEquiv (A : GL ι K) :
    ((glMapEquiv φ A : GL ι K') : Matrix ι ι K') = (A : Matrix ι ι K).map φ := rfl

omit [DecidableEq ι] in
theorem map_mulVec_comp (A : Matrix ι ι K) (v : ι → K) :
    A.map φ *ᵥ (φ ∘ v) = φ ∘ (A *ᵥ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem map_statedScalars :
    (StatedScalars ι K).map (glMapEquiv φ).toMonoidHom = StatedScalars ι K' := by
  have hsc : ∀ c : Kˣ, glMapEquiv φ (GeneralLinearGroup.scalar ι c) =
      GeneralLinearGroup.scalar ι (Units.map φ.toRingHom.toMonoidHom c) := by
    intro c
    apply Units.ext
    rw [coe_glMapEquiv, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  ext A'
  constructor
  · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
    exact ⟨_, (hsc c).symm⟩
  · rintro ⟨c', rfl⟩
    refine ⟨GeneralLinearGroup.scalar ι (Units.map φ.symm.toRingHom.toMonoidHom c'), ⟨_, rfl⟩, ?_⟩
    change glMapEquiv φ _ = _
    rw [hsc]
    congr 1
    ext
    simp

variable {Q : (ι → K) → K} {Q' : (ι → K') → K'}

include φ in
theorem isometry_glMapEquiv_iff (hQ : ∀ v, Q' (φ ∘ v) = φ (Q v)) (A : GL ι K) :
    (∀ v, Q' (((glMapEquiv φ A : GL ι K') : Matrix ι ι K') *ᵥ v) = Q' v) ↔
      ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v := by
  rw [coe_glMapEquiv]
  constructor
  · intro h v
    have e := h (φ ∘ v)
    rw [map_mulVec_comp, hQ, hQ] at e
    exact φ.injective e
  · intro h v'
    have hv : v' = φ ∘ (φ.symm ∘ v') := by
      ext i
      simp
    rw [hv, map_mulVec_comp, hQ, hQ, h]

theorem map_statedOmega (hQ : ∀ v, Q' (φ ∘ v) = φ (Q v)) :
    (StatedOmega Q).map (glMapEquiv φ).toMonoidHom = StatedOmega Q' := by
  have himg : (glMapEquiv φ).toMonoidHom '' {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} =
      {A' : GL ι K' | ∀ v, Q' ((A' : Matrix ι ι K') *ᵥ v) = Q' v} := by
    ext A'
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact (isometry_glMapEquiv_iff φ hQ A).2 hA
    · intro hA'
      refine ⟨(glMapEquiv φ).symm A', (isometry_glMapEquiv_iff φ hQ _).1 ?_, ?_⟩
      · rw [MulEquiv.apply_symm_apply]
        exact hA'
      · exact (glMapEquiv φ).apply_symm_apply A'
  rw [StatedOmega, StatedOmega, Subgroup.map_commutator, MonoidHom.map_closure, himg]

@[expose] def statedOmegaMapEquiv (hQ : ∀ v, Q' (φ ∘ v) = φ (Q v)) :
    StatedOmega Q ≃* StatedOmega Q' :=
  ((glMapEquiv φ).subgroupMap (StatedOmega Q)).trans
    (MulEquiv.subgroupCongr (map_statedOmega φ hQ))

theorem coe_statedOmegaMapEquiv (hQ : ∀ v, Q' (φ ∘ v) = φ (Q v)) (x : StatedOmega Q) :
    ((statedOmegaMapEquiv φ hQ x : StatedOmega Q') : GL ι K') = glMapEquiv φ x := rfl

theorem map_scalars_subgroupOf (hQ : ∀ v, Q' (φ ∘ v) = φ (Q v)) :
    ((StatedScalars ι K).subgroupOf (StatedOmega Q)).map
        (statedOmegaMapEquiv φ hQ : StatedOmega Q →* StatedOmega Q') =
      (StatedScalars ι K').subgroupOf (StatedOmega Q') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf]
    change ((statedOmegaMapEquiv φ hQ x : StatedOmega Q') : GL ι K') ∈ _
    rw [coe_statedOmegaMapEquiv, ← map_statedScalars φ]
    exact ⟨x, hx, rfl⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf, ← map_statedScalars φ] at hy
    obtain ⟨A, hA, hAy⟩ := hy
    refine ⟨(statedOmegaMapEquiv φ hQ).symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have e : (((statedOmegaMapEquiv φ hQ).symm y : StatedOmega Q) : GL ι K) = A := by
      apply (glMapEquiv φ).injective
      rw [← coe_statedOmegaMapEquiv φ hQ, MulEquiv.apply_symm_apply]
      exact hAy.symm
    rw [e]
    exact hA

@[expose] def statedProjOmegaMapEquiv (hQ : ∀ v, Q' (φ ∘ v) = φ (Q v)) :
    StatedProj (StatedOmega Q) ≃* StatedProj (StatedOmega Q') :=
  QuotientGroup.congr _ _ (statedOmegaMapEquiv φ hQ) (map_scalars_subgroupOf φ hQ)

end FieldMap

theorem statedQuadPlus_map {K K' : Type} [Field K] [Field K'] (φ : K ≃+* K') (n : ℕ)
    (v : Fin n ⊕ Fin n → K) : StatedQuadPlus n K' (φ ∘ v) = φ (StatedQuadPlus n K v) := by
  simp [StatedQuadPlus, map_sum, map_mul]

theorem exists_galois_coordinatePlus {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (h : StatedClassicalModel G .POmegaPlus n p f) :
    Nonempty (G ≃* matrixProjectiveDerived (coordinateQuadPlus n (GaloisField p f))) := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hKc, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField p f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc,
      GaloisField.card p f (by omega)]
  let φ : K ≃+* GaloisField p f := FiniteField.ringEquivOfCardEq hcard
  exact ⟨(e.trans (statedProjOmegaMapEquiv φ (statedQuadPlus_map φ n))).trans
    (plusCoordinateEquiv n _)⟩

end CFSG.ComponentClassification.Burgoyne.DX
