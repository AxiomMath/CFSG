module

public import Mathlib.GroupTheory.SemidirectProduct
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
import CFSG.FeitThompson.Representations.CoprimeDimProjectiveRepRescaling
import CFSG.FeitThompson.Representations.CentralElementsSeparatedIrreducibles
import CFSG.FeitThompson.Local.AveragingProjectionFixedVectors
import CFSG.FeitThompson.OddOrder.CliffordConjugateDirectSumBasis
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
public import CFSG.FeitThompson.Representations.HomogeneousCyclicQuotientIrreducible

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Matrix

section Aux

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem mulVecLin_toMatrix' (f : (n → ℂ) →ₗ[ℂ] (n → ℂ)) :
    (LinearMap.toMatrix' f).mulVecLin = f := by
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

theorem toMatrix'_mulVec (f : (n → ℂ) →ₗ[ℂ] (n → ℂ)) (x : n → ℂ) :
    LinearMap.toMatrix' f *ᵥ x = f x := by
  conv_lhs => rw [show LinearMap.toMatrix' f *ᵥ x = (LinearMap.toMatrix' f).mulVecLin x from rfl,
    mulVecLin_toMatrix']

omit [DecidableEq n] in
theorem matrix_eq_of_mulVec_eq {A B : Matrix n n ℂ} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
  classical
  have h2 : A.mulVecLin = B.mulVecLin := by ext x i; exact congrFun (h _) i
  have h3 := congrArg LinearMap.toMatrix' h2
  rwa [← Matrix.toLin'_apply', ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_toLin'] at h3

noncomputable def glOfMul {U : Type*} [Group U] (T : U → Matrix n n ℂ)
    (hu : ∀ u, IsUnit (T u).det) (h1 : T 1 = 1) (hmul : ∀ u v, T u * T v = T (u * v)) :
    U →* GL n ℂ where
  toFun u := Matrix.GeneralLinearGroup.mk'' (T u) (hu u)
  map_one' := by ext i j; simp [Matrix.GeneralLinearGroup.val_mk'', h1]
  map_mul' u v := by ext i j; simp [Matrix.GeneralLinearGroup.val_mk'', ← hmul]

@[simp]
theorem coe_glOfMul {U : Type*} [Group U] (T : U → Matrix n n ℂ)
    (hu : ∀ u, IsUnit (T u).det) (h1 : T 1 = 1) (hmul : ∀ u v, T u * T v = T (u * v)) (u : U) :
    ((glOfMul T hu h1 hmul u : GL n ℂ) : Matrix n n ℂ) = T u := by
  simp [glOfMul, Matrix.GeneralLinearGroup.val_mk'']

end Aux

theorem exists_monoidHom_of_isComplement' {L M : Type*} [Group L] [Group M] {H U : Subgroup L}
    [H.Normal] (hHU : H.IsComplement' U) (S : H →* M) (T : U →* M)
    (hcompat : ∀ (u : U) (h : H), S (MulAut.conjNormal (u : L) h) = T u * S h * (T u)⁻¹) :
    ∃ R : L →* M, (∀ h : H, R (h : L) = S h) ∧ (∀ u : U, R (u : L) = T u) := by
  have key : ∀ u : U, S.comp (MulEquiv.toMonoidHom
      (((H.normalizerMonoidHom).comp
        (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top))) u)) =
      (MulEquiv.toMonoidHom (MulAut.conj (T u))).comp S := by
    intro u
    ext h
    have hcj : (((H.normalizerMonoidHom).comp
        (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top))) u h)
          = MulAut.conjNormal (u : L) h := by
      apply Subtype.ext
      simp [Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut, MulAut.conjNormal_apply]
      rfl
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hcj, hcompat]
    simp [MulAut.conj]
  refine ⟨(SemidirectProduct.lift S T key).comp
    (SemidirectProduct.mulEquivSubgroup hHU).symm.toMonoidHom, fun h => ?_, fun u => ?_⟩
  · have h1 : (SemidirectProduct.mulEquivSubgroup hHU).symm (h : L)
        = SemidirectProduct.inl h := by
      rw [MulEquiv.symm_apply_eq]; simp [SemidirectProduct.mulEquivSubgroup_apply]
    simp [h1]
  · have h1 : (SemidirectProduct.mulEquivSubgroup hHU).symm (u : L)
        = SemidirectProduct.inr u := by
      rw [MulEquiv.symm_apply_eq]; simp [SemidirectProduct.mulEquivSubgroup_apply]
    simp [h1]

section Rep

variable {H : Type*} [Group H]

theorem exists_representation_fin_of_mem_Irr {lam : H → ℂ} (hlam : lam ∈ Irr H) {d : ℕ}
    (hd : lam 1 = d) :
    ∃ σ : Representation ℂ H (Fin d → ℂ), σ.IsIrreducible ∧ σ.character = lam := by
  obtain ⟨V, hVirr, hVchar⟩ := mem_Irr.1 hlam
  have hfr : finrank ℂ V.V = d := by
    have h := V.char_one
    rw [hVchar, hd] at h
    exact_mod_cast h.symm
  let b : Module.Basis (Fin d) ℂ V.V := (Module.finBasis ℂ V.V).reindex (finCongr hfr)
  refine ⟨conjRepresentation V.ρ b.equivFun,
    Representation.isIrreducible_of_equiv (conjRepresentationEquiv V.ρ b.equivFun) hVirr, ?_⟩
  rw [character_conjRepresentation]
  exact hVchar

theorem neZero_of_isIrreducible_fin {d : ℕ} {σ : Representation ℂ H (Fin d → ℂ)}
    (hσ : σ.IsIrreducible) : NeZero d := by
  have := hσ
  have h : Nontrivial (Fin d → ℂ) := nontrivial_of_isIrreducible σ
  refine ⟨fun hd => ?_⟩
  subst hd
  have : Subsingleton (Fin 0 → ℂ) := inferInstance
  exact absurd h (not_nontrivial _)

end Rep

variable {L : Type*} [Group L] {H U : Subgroup L} [H.Normal] {d : ℕ}

noncomputable def repMat (σ : Representation ℂ H (Fin d → ℂ)) (h : H) :
    Matrix (Fin d) (Fin d) ℂ := LinearMap.toMatrix' (σ h)

omit [H.Normal] in
theorem repMat_apply (σ : Representation ℂ H (Fin d → ℂ)) (h : H) :
    repMat σ h = LinearMap.toMatrix' (σ h) := (rfl)

omit [H.Normal] in
theorem repMat_mulVec (σ : Representation ℂ H (Fin d → ℂ)) (h : H) (x : Fin d → ℂ) :
    repMat σ h *ᵥ x = σ h x := toMatrix'_mulVec _ _

omit [H.Normal] in
theorem repMat_one (σ : Representation ℂ H (Fin d → ℂ)) : repMat σ 1 = 1 := by
  rw [repMat, show σ 1 = LinearMap.id from map_one σ, LinearMap.toMatrix'_id]

omit [H.Normal] in
theorem repMat_mul (σ : Representation ℂ H (Fin d → ℂ)) (h k : H) :
    repMat σ (h * k) = repMat σ h * repMat σ k := by
  rw [repMat, repMat, repMat, show σ (h * k) = (σ h) ∘ₗ (σ k) from map_mul σ h k,
    LinearMap.toMatrix'_comp]

omit [H.Normal] in
theorem isUnit_det_repMat (σ : Representation ℂ H (Fin d → ℂ)) (h : H) :
    IsUnit (repMat σ h).det := by
  refine IsUnit.of_mul_eq_one (b := (repMat σ h⁻¹).det) ?_
  rw [← Matrix.det_mul, ← repMat_mul, mul_inv_cancel, repMat_one, Matrix.det_one]

theorem conjNormal_one_apply (h : H) : MulAut.conjNormal (1 : L) h = h := by
  rw [map_one]; rfl

theorem conjNormal_mul_apply (x y : L) (h : H) :
    MulAut.conjNormal (H := H) (x * y) h = MulAut.conjNormal x (MulAut.conjNormal y h) := by
  rw [map_mul]; rfl

theorem conjNormal_inv_coe (u : L) (h : H) :
    ((MulAut.conjNormal (H := H) u⁻¹ h : H) : L) = u⁻¹ * (h : L) * u := by
  rw [MulAut.conjNormal_apply]; group

variable [Finite L]

theorem exists_intertwiner_matrix (σ : Representation ℂ H (Fin d → ℂ))
    (hσ : σ.IsIrreducible) (x : L)
    (hchar : ∀ h : H, σ.character (MulAut.conjNormal x h) = σ.character h) :
    ∃ B : Matrix (Fin d) (Fin d) ℂ, IsUnit B.det ∧
      ∀ h : H, B * repMat σ h = repMat σ (MulAut.conjNormal x h) * B := by
  have h1 : σ.IsIrreducible := hσ
  have h2 : (conjRep σ x).IsIrreducible := isIrreducible_conjRep hσ x
  have hce : σ.character = (conjRep σ x).character := by
    funext h
    rw [show (conjRep σ x).character h = σ.character (MulAut.conjNormal x h) by
      simp [Representation.character, conjRep_apply], hchar]
  obtain ⟨e⟩ := (nonempty_equiv_iff_character_eq σ (conjRep σ x)).2 hce
  refine ⟨LinearMap.toMatrix' (e.toLinearEquiv : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)), ?_, fun h => ?_⟩
  · rw [← LinearMap.toMatrix_eq_toMatrix']
    exact e.toLinearEquiv.isUnit_det _ _
  · rw [repMat, repMat, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun v => ?_
    have := Representation.IntertwiningMap.isIntertwining σ (conjRep σ x) e.toIntertwiningMap h v
    simpa [conjRep_apply] using this

omit [Finite L] in
theorem exists_smul_of_intertwiner_matrix [NeZero d]
    (σ : Representation ℂ H (Fin d → ℂ)) (hσ : σ.IsIrreducible) (x : L)
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : ∀ h : H, A * repMat σ h = repMat σ (MulAut.conjNormal x h) * A)
    (hB : ∀ h : H, B * repMat σ h = repMat σ (MulAut.conjNormal x h) * B)
    (hBu : IsUnit B.det) : ∃ c : ℂ, A = c • B := by
  have hne : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have h2 : (conjRep σ x).IsIrreducible := isIrreducible_conjRep hσ x
  have key : ∀ (C : Matrix (Fin d) (Fin d) ℂ),
      (∀ h : H, C * repMat σ h = repMat σ (MulAut.conjNormal x h) * C) →
      ∀ (h : H) (w : Fin d → ℂ), C.mulVecLin (σ h w) = (conjRep σ x) h (C.mulVecLin w) := by
    intro C hC h w
    have hstep : C *ᵥ (repMat σ h *ᵥ w) = repMat σ (MulAut.conjNormal x h) *ᵥ (C *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, hC, ← Matrix.mulVec_mulVec]
    rw [repMat_mulVec, repMat_mulVec] at hstep
    simpa [Matrix.mulVecLin_apply, conjRep_apply] using hstep
  have hB0 : B.mulVecLin ≠ 0 := by
    intro h0
    have hB0' : B = 0 := matrix_eq_of_mulVec_eq fun v => by
      have := congrArg (fun f : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) => f v) h0
      simpa [Matrix.mulVecLin_apply] using this
    rw [hB0'] at hBu
    simp at hBu
  obtain ⟨cc, hcc⟩ := Representation.exists_smul_eq_of_intertwiner hσ h2 A.mulVecLin B.mulVecLin
    (key A hA) (key B hB) hB0
  refine ⟨cc, matrix_eq_of_mulVec_eq fun v => ?_⟩
  rw [Matrix.smul_mulVec]
  simpa [Matrix.mulVecLin_apply] using hcc v

theorem exists_intertwiner_family [NeZero d] (σ : Representation ℂ H (Fin d → ℂ))
    (hσ : σ.IsIrreducible)
    (hchar : ∀ (u : U) (h : H), σ.character (MulAut.conjNormal (u : L) h) = σ.character h) :
    ∃ B : U → Matrix (Fin d) (Fin d) ℂ, B 1 = 1 ∧ (∀ u, IsUnit (B u).det) ∧
      ∀ (u : U) (h : H), B u * repMat σ h = repMat σ (MulAut.conjNormal (u : L) h) * B u := by
  classical
  have hex : ∀ u : U, ∃ B : Matrix (Fin d) (Fin d) ℂ, IsUnit B.det ∧
      ∀ h : H, B * repMat σ h = repMat σ (MulAut.conjNormal (u : L) h) * B :=
    fun u => exists_intertwiner_matrix σ hσ (u : L) (hchar u)
  choose B hBu hBint using hex
  refine ⟨fun u => if u = 1 then 1 else B u, by simp, fun u => ?_, fun u h => ?_⟩
  · by_cases hu : u = 1
    · simp [hu]
    · simp only [if_neg hu]; exact hBu u
  · by_cases hu : u = 1
    · subst hu; simp
    · simp only [if_neg hu]; exact hBint u h

omit [Finite L] in
theorem exists_factorSet [NeZero d] (σ : Representation ℂ H (Fin d → ℂ))
    (hσ : σ.IsIrreducible) {B : U → Matrix (Fin d) (Fin d) ℂ} (hBu : ∀ u, IsUnit (B u).det)
    (hBint : ∀ (u : U) (h : H),
      B u * repMat σ h = repMat σ (MulAut.conjNormal (u : L) h) * B u) :
    ∃ α : U → U → ℂ, (∀ u v, α u v ≠ 0) ∧ ∀ u v, B u * B v = α u v • B (u * v) := by
  classical
  have hex : ∀ u v : U, ∃ c : ℂ, c ≠ 0 ∧ B u * B v = c • B (u * v) := by
    intro u v
    have hprod : ∀ h : H, (B u * B v) * repMat σ h
        = repMat σ (MulAut.conjNormal ((u * v : U) : L) h) * (B u * B v) := by
      intro h
      calc (B u * B v) * repMat σ h
          = B u * (B v * repMat σ h) := by rw [mul_assoc]
        _ = B u * (repMat σ (MulAut.conjNormal (v : L) h) * B v) := by rw [hBint]
        _ = (B u * repMat σ (MulAut.conjNormal (v : L) h)) * B v := by rw [mul_assoc]
        _ = (repMat σ (MulAut.conjNormal (u : L) (MulAut.conjNormal (v : L) h)) * B u) * B v := by
              rw [hBint]
        _ = repMat σ (MulAut.conjNormal ((u * v : U) : L) h) * (B u * B v) := by
              rw [mul_assoc, ← conjNormal_mul_apply]; norm_cast
    obtain ⟨c, hc⟩ := exists_smul_of_intertwiner_matrix σ hσ ((u * v : U) : L)
      hprod (hBint (u * v)) (hBu (u * v))
    refine ⟨c, ?_, hc⟩
    intro hc0
    rw [hc0, zero_smul] at hc
    have hdet := (hBu u).mul (hBu v)
    rw [← Matrix.det_mul, hc] at hdet
    simp at hdet
  choose α hα0 hα using hex
  exact ⟨α, hα0, hα⟩

theorem exists_linearized_intertwiner_family [NeZero d]
    (σ : Representation ℂ H (Fin d → ℂ)) (hσ : σ.IsIrreducible)
    (hcop : d.Coprime (Nat.card U))
    (hchar : ∀ (u : U) (h : H), σ.character (MulAut.conjNormal (u : L) h) = σ.character h) :
    ∃ T : U → Matrix (Fin d) (Fin d) ℂ, T 1 = 1 ∧ (∀ u, IsUnit (T u).det) ∧
      (∀ u v, T u * T v = T (u * v)) ∧
      ∀ (u : U) (h : H), T u * repMat σ h = repMat σ (MulAut.conjNormal (u : L) h) * T u := by
  have hne : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  obtain ⟨B, hB1, hBu, hBint⟩ := exists_intertwiner_family σ hσ (U := U) hchar
  obtain ⟨α, hα0, hα⟩ := exists_factorSet σ hσ hBu hBint
  have hcop' : (Fintype.card (Fin d)).Coprime (Nat.card U) := by simpa using hcop
  obtain ⟨c, hc1, hc0, hcmul⟩ :=
    exists_matrix_projLinearization (B := B) (α := α) hcop' hBu hB1 hα0 hα
  refine ⟨fun u => (c u)⁻¹ • B u, by simp [hc1, hB1], fun u => ?_, fun u v => ?_, fun u h => ?_⟩
  · rw [Matrix.det_smul]
    exact (Ne.isUnit (pow_ne_zero _ (inv_ne_zero (hc0 u)))).mul (hBu u)
  · exact hcmul u v
  · rw [Matrix.smul_mul, hBint, Matrix.mul_smul]

omit [Finite L] in
theorem exists_mem_Irr_resClassFun_eq_character [NeZero d]
    (σ : Representation ℂ H (Fin d → ℂ)) (hσ : σ.IsIrreducible) (hHU : H.IsComplement' U)
    {T : U → Matrix (Fin d) (Fin d) ℂ} (hT1 : T 1 = 1) (hTu : ∀ u, IsUnit (T u).det)
    (hTmul : ∀ u v, T u * T v = T (u * v))
    (hTint : ∀ (u : U) (h : H),
      T u * repMat σ h = repMat σ (MulAut.conjNormal (u : L) h) * T u) :
    ∃ eta ∈ Irr L, resClassFun H eta = σ.character := by
  set S : H →* GL (Fin d) ℂ :=
    glOfMul (repMat σ) (isUnit_det_repMat σ) (repMat_one σ) (fun h k => (repMat_mul σ h k).symm)
    with hS
  set T' : U →* GL (Fin d) ℂ := glOfMul T hTu hT1 hTmul with hT'
  have hcompat : ∀ (u : U) (h : H), S (MulAut.conjNormal (u : L) h) = T' u * S h * (T' u)⁻¹ := by
    intro u h
    have hmat : (T' u : Matrix (Fin d) (Fin d) ℂ) * (S h : Matrix (Fin d) (Fin d) ℂ)
        = (S (MulAut.conjNormal (u : L) h) : Matrix (Fin d) (Fin d) ℂ)
          * (T' u : Matrix (Fin d) (Fin d) ℂ) := by
      simpa [hS, hT'] using hTint u h
    have heq : T' u * S h = S (MulAut.conjNormal (u : L) h) * T' u := by
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      simpa using congrFun (congrFun hmat i) j
    rw [eq_mul_inv_iff_mul_eq, ← heq]
  obtain ⟨R, hRH, -⟩ := exists_monoidHom_of_isComplement' hHU S T' hcompat
  have hR : ∀ h : H, ((R (h : L) : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) = repMat σ h := by
    intro h; rw [hRH h]; simp [hS]
  have hres : ∀ h : H, (glRepresentation R) (h : L) = σ h := by
    intro h
    rw [glRepresentation_apply, hR h, repMat, mulVecLin_toMatrix']
  have hirr : (glRepresentation R).IsIrreducible := by
    have hne : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
    have hnt : Nontrivial (Fin d → ℂ) := inferInstance
    refine isIrreducible_of_forall_map_le (fun W hW => ?_)
    rcases eq_or_ne W ⊥ with h | h
    · exact Or.inl h
    · refine Or.inr (eq_top_of_isIrreducible_of_map_le hσ (fun g => ?_) h)
      rw [← hres g]
      exact hW (g : L)
  refine ⟨(glRepresentation R).character, character_mem_Irr_of_isIrreducible _ hirr, ?_⟩
  funext h
  rw [resClassFun_apply, Representation.character, Representation.character, hres]

theorem exists_mem_Irr_resClassFun_eq {lam : H → ℂ} (hlam : lam ∈ Irr H) (hd : lam 1 = d)
    (hsup : H ⊔ U = ⊤) (hinf : H ⊓ U = ⊥) (hcop : d.Coprime (Nat.card U))
    (hinv : ∀ (u : U) (h : H), lam (MulAut.conjNormal ((u : L))⁻¹ h) = lam h) :
    ∃ eta ∈ Irr L, resClassFun H eta = lam := by
  have hHU : H.IsComplement' U := (isComplement'_of_sup_eq_top_of_inf_eq_bot hsup hinf).symm
  obtain ⟨σ, hσ, hσchar⟩ := exists_representation_fin_of_mem_Irr hlam hd
  have hne : NeZero d := neZero_of_isIrreducible_fin hσ
  have hchar : ∀ (u : U) (h : H), σ.character (MulAut.conjNormal (u : L) h) = σ.character h := by
    intro u h
    rw [hσchar]
    simpa using hinv u⁻¹ h
  obtain ⟨T, hT1, hTu, hTmul, hTint⟩ :=
    exists_linearized_intertwiner_family σ hσ (U := U) hcop hchar
  obtain ⟨eta, hetaIrr, hetares⟩ :=
    exists_mem_Irr_resClassFun_eq_character σ hσ hHU hT1 hTu hTmul hTint
  exact ⟨eta, hetaIrr, by rw [hetares, hσchar]⟩

end CFSG.FeitThompson
