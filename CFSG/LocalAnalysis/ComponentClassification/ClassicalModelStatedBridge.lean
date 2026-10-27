module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.PGLModelStated

public noncomputable section

namespace CFSG.ComponentClassification.ClassicalModelStatedBridge

open Matrix
open CFSG.Assembly.ComponentType (omegaModel pslModel psuModel pspModel quadOdd quadPlus quadMinus)
open CFSG.Assembly.LowTwoRank

section Projective

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {K : Type}
  [Field K]

export CFSG.Open.StatedAPI (ker_mk_comp_subtype mapMkEquivStatedProj
  coe_mapMkEquivStatedProj_symm_mk mapMkEquivStatedProj_mk)

@[expose] def glReindex (K : Type) [Field K] (e : ι ≃ ι') : GL ι K ≃* GL ι' K :=
  Units.mapEquiv (reindexRingEquiv K e).toMulEquiv

@[simp] theorem coe_glReindex (e : ι ≃ ι') (A : GL ι K) :
    ((glReindex K e A : GL ι' K) : Matrix ι' ι' K) = reindex e e (A : Matrix ι ι K) :=
  rfl

@[simp] theorem coe_glReindex_symm (e : ι ≃ ι') (A : GL ι' K) :
    (((glReindex K e).symm A : GL ι K) : Matrix ι ι K) =
      reindex e.symm e.symm (A : Matrix ι' ι' K) :=
  rfl

@[expose] def pglReindex (K : Type) [Field K] (e : ι ≃ ι') :
    ProjGenLinGroup ι K ≃* ProjGenLinGroup ι' K :=
  QuotientGroup.congr _ _ (glReindex K e) (Subgroup.map_center_eq (glReindex K e))

@[simp] theorem pglReindex_mk (e : ι ≃ ι') (A : GL ι K) :
    pglReindex K e (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk (glReindex K e A) :=
  rfl

@[simp] theorem pglReindex_symm_mk (e : ι ≃ ι') (A : GL ι' K) :
    (pglReindex K e).symm (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk ((glReindex K e).symm A) :=
  rfl

theorem map_pglReindex_map_mk (e : ι ≃ ι') (H : Subgroup (GL ι K)) :
    (H.map (ProjGenLinGroup.mk : GL ι K →* ProjGenLinGroup ι K)).map
        (pglReindex K e : ProjGenLinGroup ι K →* ProjGenLinGroup ι' K) =
      (H.map (glReindex K e : GL ι K →* GL ι' K)).map ProjGenLinGroup.mk := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem image_glReindex_isometries (e : ι ≃ ι') {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = Q' (v ∘ e.symm)) :
    glReindex K e '' {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} =
      {A : GL ι' K | ∀ v, Q' ((A : Matrix ι' ι' K) *ᵥ v) = Q' v} := by
  have key (A : GL ι' K) :
      (∀ v, Q ((((glReindex K e).symm A : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v) ↔
        ∀ v, Q' ((A : Matrix ι' ι' K) *ᵥ v) = Q' v := by
    simp only [coe_glReindex_symm, reindex_apply, Equiv.symm_symm, hQ, submatrix_mulVec_equiv]
    constructor
    · intro h w
      simpa [Function.comp_assoc] using h (w ∘ e)
    · intro h v
      simpa [Function.comp_assoc] using h (v ∘ e.symm)
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (key _).1 (by simpa using hB)
  · intro hA
    exact ⟨(glReindex K e).symm A, (key A).2 hA, MulEquiv.apply_symm_apply _ _⟩

theorem map_glReindex_orthogonalGroup (e : ι ≃ ι') {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = Q' (v ∘ e.symm)) :
    (Assembly.ComponentType.orthogonalGroup Q).map (glReindex K e : GL ι K →* GL ι' K) =
      Subgroup.closure {A : GL ι' K | ∀ v, Q' ((A : Matrix ι' ι' K) *ᵥ v) = Q' v} := by
  rw [Assembly.ComponentType.orthogonalGroup, MonoidHom.map_closure]
  exact congrArg Subgroup.closure (image_glReindex_isometries e hQ)

theorem map_glReindex_commutator_orthogonalGroup (e : ι ≃ ι') {Q : (ι → K) → K}
    {Q' : (ι' → K) → K} (hQ : ∀ v, Q v = Q' (v ∘ e.symm)) :
    ⁅Assembly.ComponentType.orthogonalGroup Q, Assembly.ComponentType.orthogonalGroup Q⁆.map
        (glReindex K e : GL ι K →* GL ι' K) = StatedOmega Q' := by
  rw [Subgroup.map_commutator, map_glReindex_orthogonalGroup e hQ]
  rfl

@[expose] def omegaModelEquivOfReindex (e : ι ≃ ι') {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = Q' (v ∘ e.symm)) : omegaModel Q ≃* StatedProj (StatedOmega Q') :=
  ((pglReindex K e).subgroupMap (omegaModel Q)).trans
    ((MulEquiv.subgroupCongr (by
      rw [omegaModel, map_pglReindex_map_mk, map_glReindex_commutator_orthogonalGroup e hQ])).trans
      (mapMkEquivStatedProj (StatedOmega Q')))

@[simp] theorem coe_omegaModelEquivOfReindex_symm_mk (e : ι ≃ ι') {Q : (ι → K) → K}
    {Q' : (ι' → K) → K} (hQ : ∀ v, Q v = Q' (v ∘ e.symm)) (A : StatedOmega Q') :
    ((omegaModelEquivOfReindex e hQ).symm (A : StatedProj (StatedOmega Q')) :
        ProjGenLinGroup ι K) = ProjGenLinGroup.mk ((glReindex K e).symm A) :=
  rfl

end Projective

section Models

variable (n p f : ℕ) [Fact p.Prime]

export CFSG.Open.StatedAPI (statedSL_eq_ker_det)

@[expose] def pslModelEquiv : pslModel n p f ≃* StatedProj (StatedSL n (GaloisField p f)) :=
  (MulEquiv.subgroupCongr
      (by rw [pslModel, PGLModel.projSL, PGLModel.projImage, statedSL_eq_ker_det])).trans
    (mapMkEquivStatedProj _)

@[simp] theorem coe_pslModelEquiv_symm_mk (A : StatedSL n (GaloisField p f)) :
    ((pslModelEquiv n p f).symm (A : StatedProj (StatedSL n (GaloisField p f))) :
        ProjGenLinGroup (Fin n) (GaloisField p f)) = ProjGenLinGroup.mk (A : GL _ _) :=
  rfl

theorem psuModel_eq_map_mk :
    psuModel n p f = (StatedSU n (p ^ f) (GaloisField p (2 * f))).map ProjGenLinGroup.mk :=
  (CFSG.PGLModel.projImage_statedSU n p f).symm

@[expose] def psuModelEquiv :
    psuModel n p f ≃* StatedProj (StatedSU n (p ^ f) (GaloisField p (2 * f))) :=
  (MulEquiv.subgroupCongr (psuModel_eq_map_mk n p f)).trans (mapMkEquivStatedProj _)

@[simp] theorem coe_psuModelEquiv_symm_mk (A : StatedSU n (p ^ f) (GaloisField p (2 * f))) :
    ((psuModelEquiv n p f).symm (A : StatedProj (StatedSU n (p ^ f) (GaloisField p (2 * f)))) :
        ProjGenLinGroup (Fin n) (GaloisField p (2 * f))) = ProjGenLinGroup.mk (A : GL _ _) :=
  rfl

theorem pspModel_eq_map_mk :
    pspModel n p f = (StatedSp n (GaloisField p f)).map ProjGenLinGroup.mk :=
  rfl

@[expose] def pspModelEquiv : pspModel n p f ≃* StatedProj (StatedSp n (GaloisField p f)) :=
  (MulEquiv.subgroupCongr (pspModel_eq_map_mk n p f)).trans (mapMkEquivStatedProj _)

@[simp] theorem coe_pspModelEquiv_symm_mk (A : StatedSp n (GaloisField p f)) :
    ((pspModelEquiv n p f).symm (A : StatedProj (StatedSp n (GaloisField p f))) :
        ProjGenLinGroup (Fin n ⊕ Fin n) (GaloisField p f)) = ProjGenLinGroup.mk (A : GL _ _) :=
  rfl

end Models

section Orthogonal

variable (n : ℕ) (K : Type) [Field K]

theorem quadOdd_eq_comp (v : (Fin n ⊕ Fin n) ⊕ Unit → K) :
    quadOdd n K v = StatedQuadOdd n K (v ∘ (Equiv.sumAssoc _ _ _).symm) :=
  rfl

@[expose] def omegaModelOddEquiv :
    omegaModel (quadOdd n K) ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) :=
  omegaModelEquivOfReindex (Equiv.sumAssoc _ _ _) (quadOdd_eq_comp n K)

@[simp] theorem coe_omegaModelOddEquiv_symm_mk (A : StatedOmega (StatedQuadOdd n K)) :
    ((omegaModelOddEquiv n K).symm (A : StatedProj (StatedOmega (StatedQuadOdd n K))) :
        ProjGenLinGroup ((Fin n ⊕ Fin n) ⊕ Unit) K) =
      ProjGenLinGroup.mk ((glReindex K (Equiv.sumAssoc _ _ _)).symm A) :=
  rfl

@[expose] def omegaModelPlusEquiv :
    omegaModel (quadPlus n K) ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) :=
  (MulEquiv.subgroupCongr
      (rfl : omegaModel (quadPlus n K) = (StatedOmega (StatedQuadPlus n K)).map _)).trans
    (mapMkEquivStatedProj _)

@[simp] theorem coe_omegaModelPlusEquiv_symm_mk (A : StatedOmega (StatedQuadPlus n K)) :
    ((omegaModelPlusEquiv n K).symm (A : StatedProj (StatedOmega (StatedQuadPlus n K))) :
        ProjGenLinGroup (Fin n ⊕ Fin n) K) = ProjGenLinGroup.mk (A : GL _ _) :=
  rfl

variable {K}

theorem quadMinus_eq_comp (b c : K) (v : (Fin (n - 1) ⊕ Fin (n - 1)) ⊕ Fin 2 → K) :
    quadMinus n b c v = StatedQuadMinus n K b c (v ∘ (Equiv.sumAssoc _ _ _).symm) :=
  rfl

@[expose] def omegaModelMinusEquiv (b c : K) :
    omegaModel (quadMinus n b c) ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) :=
  omegaModelEquivOfReindex (Equiv.sumAssoc _ _ _) (quadMinus_eq_comp n b c)

@[simp] theorem coe_omegaModelMinusEquiv_symm_mk (b c : K)
    (A : StatedOmega (StatedQuadMinus n K b c)) :
    ((omegaModelMinusEquiv n b c).symm (A : StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
        ProjGenLinGroup ((Fin (n - 1) ⊕ Fin (n - 1)) ⊕ Fin 2) K) =
      ProjGenLinGroup.mk ((glReindex K (Equiv.sumAssoc _ _ _)).symm A) :=
  rfl

end Orthogonal

@[expose] def ClassicalTag.toStated : Assembly.ComponentType.ClassicalTag → StatedLieTag
  | .PSL => .PSL
  | .PSU => .PSU
  | .PSp => .PSp
  | .POmegaOdd => .POmegaOdd
  | .POmegaPlus => .POmegaPlus
  | .POmegaMinus => .POmegaMinus

theorem statedClassicalModel_of_classicalModel {X : Type} [Group X]
    (t : Assembly.ComponentType.ClassicalTag) (n p f : ℕ) [Fact p.Prime]
    (h : Assembly.ComponentType.ClassicalModel X t n p f) :
    StatedClassicalModel X (ClassicalTag.toStated t) n p f := by
  obtain ⟨hadm, hX⟩ := h
  cases t with
  | PSL =>
    obtain ⟨hp, hf, hn, hq⟩ := hadm
    obtain ⟨e⟩ := hX
    exact ⟨⟨hp, hf, hn, fun h => hq ⟨(Prod.mk.inj h).1, .inl (Prod.mk.inj h).2⟩,
        fun h => hq ⟨(Prod.mk.inj h).1, .inr (Prod.mk.inj h).2⟩⟩,
      GaloisField p f, inferInstance, inferInstance, GaloisField.card p f (by omega),
      ⟨e.trans (pslModelEquiv n p f)⟩⟩
  | PSU =>
    obtain ⟨hp, hf, hn, hq⟩ := hadm
    obtain ⟨e⟩ := hX
    exact ⟨⟨hp, hf, hn, fun h => hq (Prod.mk.inj h)⟩,
      GaloisField p (2 * f), inferInstance, inferInstance,
      by rw [GaloisField.card p (2 * f) (by omega), mul_comm, pow_mul],
      ⟨e.trans (psuModelEquiv n p f)⟩⟩
  | PSp =>
    obtain ⟨hp, hf, hn, hq⟩ := hadm
    obtain ⟨e⟩ := hX
    exact ⟨⟨hp, hf, hn, fun h => hq (Prod.mk.inj h)⟩,
      GaloisField p f, inferInstance, inferInstance, GaloisField.card p f (by omega),
      ⟨e.trans (pspModelEquiv n p f)⟩⟩
  | POmegaOdd =>
    obtain ⟨hp, hf, hn⟩ := hadm
    obtain ⟨e⟩ := hX
    exact ⟨⟨hp, hf, hn⟩, GaloisField p f, inferInstance, inferInstance,
      GaloisField.card p f (by omega), ⟨e.trans (omegaModelOddEquiv n _)⟩⟩
  | POmegaPlus =>
    obtain ⟨hp, hf, hn⟩ := hadm
    obtain ⟨e⟩ := hX
    exact ⟨⟨hp, hf, hn⟩, GaloisField p f, inferInstance, inferInstance,
      GaloisField.card p f (by omega), ⟨e.trans (omegaModelPlusEquiv n _)⟩⟩
  | POmegaMinus =>
    obtain ⟨hp, hf, hn⟩ := hadm
    obtain ⟨b, c, hbc, ⟨e⟩⟩ := hX
    exact ⟨⟨hp, hf, hn⟩, GaloisField p f, inferInstance, inferInstance,
      GaloisField.card p f (by omega), b, c, hbc, ⟨e.trans (omegaModelMinusEquiv n b c)⟩⟩

end CFSG.ComponentClassification.ClassicalModelStatedBridge
