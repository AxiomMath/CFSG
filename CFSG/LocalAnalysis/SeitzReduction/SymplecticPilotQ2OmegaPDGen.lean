module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCExt
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions (commSpace omegaGroup mem_omegaGroup)
open CFSG.RankThree.Classical2 (orthDerived)

section Dickson

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] noncomputable def pdLinEquiv : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

theorem pdLinEquiv_apply (N : GL ι K) (v : ι → K) : pdLinEquiv N v = (N : Matrix ι ι K) *ᵥ v :=
  rfl

theorem pd_commSpace_eq (N : GL ι K) :
    commSpace (pdLinEquiv N) = LinearMap.range ((N : Matrix ι ι K) - 1).mulVecLin := by
  ext v
  simp [pdLinEquiv_apply]

theorem pdEven_rank_of_mem_statedOmega [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : Q.polarBilin.Nondegenerate) {A : GL ι K} (hA : A ∈ StatedOmega ⇑Q) :
    Even (((A : Matrix ι ι K) - 1).rank) := by
  have hC : closure {B : GL ι K | ∀ v, Q ((B : Matrix ι ι K) *ᵥ v) = Q v} ≤
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap pdLinEquiv.toMonoidHom := by
    rw [closure_le]
    intro B hB
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [MulEquiv.coe_toMonoidHom, pdLinEquiv_apply]
      exact hB v
  have hmem : pdLinEquiv A ∈ orthDerived Q := by
    have hmap : (StatedOmega ⇑Q).map pdLinEquiv.toMonoidHom ≤ orthDerived Q := by
      rw [StatedOmega, Subgroup.map_commutator]
      exact commutator_mono (map_le_iff_le_comap.mpr hC) (map_le_iff_le_comap.mpr hC)
    exact hmap ⟨A, hA, rfl⟩
  have hev := (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ hmem).2
  rw [Matrix.rank, ← pd_commSpace_eq]
  exact hev

theorem pdMem_statedOmega_of_even [Finite K] [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {A : GL ι K}
    (hA : ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v) (hev : Even (((A : Matrix ι ι K) - 1).rank)) :
    A ∈ StatedOmega ⇑Q := by
  have hO : pdLinEquiv A ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [pdLinEquiv_apply]; exact hA v
  have hΩ : pdLinEquiv A ∈ omegaGroup Q hQ := mem_omegaGroup.mpr ⟨hO, by
    rw [pd_commSpace_eq]
    exact hev⟩
  have hD := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT hΩ
  have hC : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      (closure {B : GL ι K | ∀ v, Q ((B : Matrix ι ι K) *ᵥ v) = Q v}).map
        pdLinEquiv.toMonoidHom := by
    intro g hg
    refine ⟨pdLinEquiv.symm g, subset_closure fun v => ?_, by simp⟩
    rw [← pdLinEquiv_apply, MulEquiv.apply_symm_apply]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg v
  have hmap : orthDerived Q ≤ (StatedOmega ⇑Q).map pdLinEquiv.toMonoidHom := by
    rw [StatedOmega, Subgroup.map_commutator]
    exact commutator_mono hC hC
  obtain ⟨A', hA', hAA'⟩ := hmap hD
  rw [MulEquiv.coe_toMonoidHom] at hAA'
  rwa [← pdLinEquiv.injective hAA']

theorem pdMul_self_mem_statedOmega [Finite K] [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {B : GL ι K}
    (hB : ∀ v, Q ((B : Matrix ι ι K) *ᵥ v) = Q v) : B * B ∈ StatedOmega ⇑Q := by
  have hBB : ∀ v, Q (((B * B : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := fun v => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hB, hB]
  refine pdMem_statedOmega_of_even Q hQ hT hBB ?_
  have hO : pdLinEquiv B ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [pdLinEquiv_apply]; exact hB v
  have h := CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hO hO
  rw [← map_mul, pd_commSpace_eq, ← Matrix.rank] at h
  rw [← ZMod.natCast_eq_zero_iff_even, h, CharTwo.add_self_eq_zero]

theorem pd_exists_totallySingular_of (Q : QuadraticForm K (ι → K)) (f : Fin 3 → ι)
    (hf : Function.Injective f) (h0 : ∀ v : ι → K, (∀ i, i ∉ Set.range f → v i = 0) → Q v = 0) :
    ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  let g : Fin 3 → ι → K := fun k => Pi.single (f k) 1
  have hg : LinearIndependent K g := by
    convert (Pi.basisFun K ι).linearIndependent.comp f hf using 1
    funext k
    simp [g]
  let S : Submodule K (ι → K) :=
    { carrier := {v | ∀ i, i ∉ Set.range f → v i = 0}
      add_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
      zero_mem' := fun i _ => rfl
      smul_mem' := fun c v hv i hi => by simp [hv i hi] }
  refine ⟨Submodule.span K (Set.range g), ?_, fun x hx => h0 x ?_⟩
  · rw [finrank_span_eq_card hg, Fintype.card_fin]
  · have hle : Submodule.span K (Set.range g) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩ i hi
      have hne : i ≠ f k := fun h => hi ⟨k, h.symm⟩
      simp [g, hne]
    exact hle hx

end Dickson

section Sym

open CFSG.ClassicalGroups.Orthogonal (reflect reflect_apply reflect_mul_self
  reflect_mem_orthogonalGroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv reindexMatrixEquiv reindexMatrixEquiv_mulVec reindexQuadraticForm_map)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv_val)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL symmetryGL_mulVec_of_charTwo
  symmetryGL_mul_self)

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] noncomputable def pdSym (Q : QuadraticForm K (ι → K)) (v : ι → K) : GL ι K :=
  pdLinEquiv.symm (reflect Q v)

theorem pdSym_mulVec (Q : QuadraticForm K (ι → K)) (v x : ι → K) :
    (pdSym Q v : Matrix ι ι K) *ᵥ x = reflect Q v x := by
  rw [← pdLinEquiv_apply, pdSym, MulEquiv.apply_symm_apply]

theorem pdSym_mulVec_of_charTwo [CharP K 2] {Q : QuadraticForm K (ι → K)} {v : ι → K}
    (hv : Q v = 1) (x : ι → K) : (pdSym Q v : Matrix ι ι K) *ᵥ x = x + polar Q v x • v := by
  rw [pdSym_mulVec, reflect_apply (by rw [hv]; exact one_ne_zero), hv, div_one, sub_eq_add_neg,
    ← neg_smul, CharTwo.neg_eq]

theorem pdSym_mul_self (Q : QuadraticForm K (ι → K)) (v : ι → K) : pdSym Q v * pdSym Q v = 1 := by
  apply pdLinEquiv.injective
  rw [map_mul, pdSym, MulEquiv.apply_symm_apply, reflect_mul_self, map_one]

omit [Fintype ι] [DecidableEq ι] in
theorem pd_polar_reindexQuadraticForm {d : ℕ} (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    (v w : ι → K) :
    polar (reindexQuadraticForm e Q) (reindexVectorEquiv e v) (reindexVectorEquiv e w) =
      polar Q v w := by
  simp only [QuadraticMap.polar, ← map_add, reindexQuadraticForm_map]

theorem pd_reindexMatrixEquiv_pdSym [CharP K 2] {d : ℕ} (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {v : ι → K} (hv : Q v = 1) :
    reindexMatrixEquiv eI (pdSym Q v) =
      symmetryGL (reindexQuadraticForm eI Q) (reindexVectorEquiv eI v) := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨y, rfl⟩ := (reindexVectorEquiv (K := K) eI).surjective x
  have hv' : reindexQuadraticForm eI Q (reindexVectorEquiv eI v) = 1 := by
    rw [reindexQuadraticForm_map, hv]
  rw [symmetryGL_mulVec_of_charTwo hv', pd_polar_reindexQuadraticForm]
  have h1 := reindexMatrixEquiv_mulVec eI (pdSym Q v) y
  rw [matrixLinearEquiv_apply] at h1
  rw [h1, ← map_smul, ← map_add]
  congr 1
  exact pdSym_mulVec_of_charTwo hv y

theorem pd_coe_omegaSymmetryAut [CharP K 2] {d : ℕ} (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (h : matrixDerivedScalars (reindexQuadraticForm eI Q) = ⊥) {v : ι → K} (hv : Q v = 1)
    (A : StatedOmega Q0) :
    ((F4Pilot.omegaSymmetryAut eI Q hQ h v A : StatedOmega Q0) : GL ι K) =
      pdSym Q v * (A : GL ι K) * pdSym Q v := by
  set Q' := reindexQuadraticForm eI Q with hQ'
  have key := F4Pilot.omegaProjEquiv_omegaSymmetryAut eI Q hQ h v A
  rw [F4Pilot.omegaProjEquiv_apply, F4Pilot.omegaProjEquiv_apply] at key
  change _ = matrixProjectiveConjugation Q' _ (matrixProjectiveProjection Q' _) at key
  rw [matrixProjectiveConjugation_mk, (F4Pilot.matrixProjectiveProjection_injective h).eq_iff]
    at key
  have key2 := congrArg Subtype.val key
  rw [statedDerivedReindexEquiv_val, matrixDerivedConjugation_val, matrixIsometryInclusion_val,
    statedDerivedReindexEquiv_val] at key2
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
    MulAut.one_apply] at key2
  apply (reindexMatrixEquiv (K := K) eI).injective
  rw [key2, map_mul, map_mul, pd_reindexMatrixEquiv_pdSym eI Q hv,
    inv_eq_of_mul_eq_one_right (symmetryGL_mul_self _ _)]

end Sym

section Ext

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {K : Type}
  [Field K] {M : Matrix κ ι K} {R : Matrix ι κ K}

omit [DecidableEq ι] [DecidableEq κ] in
theorem pcExt_polar {Qg : QuadraticForm K (κ → K)} {Qm : QuadraticForm K (ι → K)}
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x)) (x : κ → K)
    (y : ι → K) : polar Qg x (M *ᵥ y) = polar Qm (R *ᵥ x) y := by
  have h0 := hQ 0 y
  simp only [zero_add, Matrix.mulVec_zero, QuadraticMap.map_zero, sub_zero] at h0
  simp only [QuadraticMap.polar, h0]
  linear_combination hQ x y

theorem pcExtMat_mulVec_of_proj (g : Matrix ι ι K) {x : κ → K} (hx : R *ᵥ x = 0) :
    pcExtMat M R g *ᵥ x = x := by
  rw [pcExtMat_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.mulVec_zero, add_zero]

theorem pcExtMat_commute {C : Matrix κ κ K} (hCM : C * M = M) (hRC : R * C = R)
    (g : Matrix ι ι K) : C * pcExtMat M R g = pcExtMat M R g * C := by
  simp only [pcExtMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  calc C * (M * (g - 1) * R) = (C * M) * (g - 1) * R := by simp only [Matrix.mul_assoc]
    _ = M * (g - 1) * (R * C) := by rw [hCM, hRC]
    _ = M * (g - 1) * R * C := by simp only [Matrix.mul_assoc]

theorem pcExtMat_conj_eq {S : Matrix κ κ K} {s : Matrix ι ι K} (hSM : S * M = M * s)
    (hRS : R * S = s * R) (hS : S * S = 1) (hs : s * s = 1) (g : Matrix ι ι K) :
    pcExtMat M R (s * g * s) = S * pcExtMat M R g * S := by
  have e1 : s * g * s - 1 = s * (g - 1) * s := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hs]
  have e2 : S * (M * (g - 1) * R) * S = M * (s * (g - 1) * s) * R := by
    calc S * (M * (g - 1) * R) * S = (S * M) * (g - 1) * (R * S) := by
          simp only [Matrix.mul_assoc]
      _ = M * (s * (g - 1) * s) * R := by
          rw [hSM, hRS]
          simp only [Matrix.mul_assoc]
  simp only [pcExtMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hS, e1, e2]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem pd_commutator_le_self {X : Type*} [Group X] (H : Subgroup X) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

omit [Fintype ι] [DecidableEq ι] in
theorem pd_isometry_of_mem_statedOmega {Q0 : (κ → K) → K} {A : GL κ K}
    (hA : A ∈ StatedOmega Q0) (x : κ → K) : Q0 ((A : Matrix κ κ K) *ᵥ x) = Q0 x := by
  let S : Subgroup (GL κ K) :=
    { carrier := {B | ∀ v, Q0 ((B : Matrix κ κ K) *ᵥ v) = Q0 v}
      mul_mem' := fun {a b} ha hb v => by rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
      one_mem' := fun v => by rw [Units.val_one, Matrix.one_mulVec]
      inv_mem' := fun {a} ha v => by
        have h1 := ha (((a⁻¹ : GL κ K) : Matrix κ κ K) *ᵥ v)
        rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec, eq_comm] at h1 }
  have hle : closure {B : GL κ K | ∀ v, Q0 ((B : Matrix κ κ K) *ᵥ v) = Q0 v} ≤ S :=
    (closure_le S).2 fun _ hB => hB
  exact hle (pd_commutator_le_self _ hA) x

omit [DecidableEq κ] in
theorem pd_rank_conj (hRM : R * M = 1) (X : Matrix ι ι K) : (M * X * R).rank = X.rank := by
  refine le_antisymm ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)) ?_
  have h : X = R * (M * X * R) * M := by
    calc X = (R * M) * X * (R * M) := by rw [hRM, Matrix.one_mul, Matrix.mul_one]
      _ = R * (M * X * R) * M := by simp only [Matrix.mul_assoc]
  calc X.rank = (R * (M * X * R) * M).rank := by rw [← h]
    _ ≤ (M * X * R).rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem pd_matrix_ext_mulVec {A B : Matrix κ κ K} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h1

theorem pcExtMat_eq_of_fix (hRM : R * M = 1) {Qg : QuadraticForm K (κ → K)}
    {Qm : QuadraticForm K (ι → K)}
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x))
    (hker : ∀ z, R *ᵥ z = 0 → (∀ x, R *ᵥ x = 0 → polar Qg z x = 0) → z = 0)
    {A : Matrix κ κ K} (hAiso : ∀ x, Qg (A *ᵥ x) = Qg x) (hfix : ∀ x, R *ᵥ x = 0 → A *ᵥ x = x) :
    (∀ y, A *ᵥ (M *ᵥ y) = M *ᵥ ((R * A * M) *ᵥ y)) ∧ A = pcExtMat M R (R * A * M) := by
  have hpol : ∀ x y, polar Qg (A *ᵥ x) (A *ᵥ y) = polar Qg x y := fun x y => by
    simp only [QuadraticMap.polar, ← Matrix.mulVec_add, hAiso]
  have hM0 : ∀ x w, R *ᵥ x = 0 → polar Qg (M *ᵥ w) x = 0 := fun x w hx => by
    rw [QuadraticMap.polar_comm, pcExt_polar hQ, hx, QuadraticMap.polar_zero_left]
  have hAM : ∀ y, A *ᵥ (M *ᵥ y) = M *ᵥ ((R * A * M) *ᵥ y) := by
    intro y
    obtain ⟨w, hw⟩ : ∃ w, w = A *ᵥ (M *ᵥ y) := ⟨_, rfl⟩
    have hRw : (R * A * M) *ᵥ y = R *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [hRw, ← hw]
    have hz : R *ᵥ (w - M *ᵥ (R *ᵥ w)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hRM, Matrix.one_mulVec, sub_self]
    have h0 := hker _ hz fun x hx => by
      rw [QuadraticMap.polar_sub_left, hM0 x _ hx, sub_zero, hw, ← hfix x hx, hpol, hM0 x _ hx]
    exact sub_eq_zero.1 h0
  refine ⟨hAM, pd_matrix_ext_mulVec fun x => ?_⟩
  have hx : x = (x - M *ᵥ (R *ᵥ x)) + M *ᵥ (R *ᵥ x) := (sub_add_cancel _ _).symm
  have hk : R *ᵥ (x - M *ᵥ (R *ᵥ x)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hRM, Matrix.one_mulVec, sub_self]
  rw [pcExtMat_mulVec]
  conv_lhs => rw [hx]
  rw [Matrix.mulVec_add, hfix _ hk, hAM, Matrix.mulVec_sub]
  abel

theorem exists_pcExtMat_eq_of_fix [Finite K] [CharP K 2] (hRM : R * M = 1)
    {Qg : QuadraticForm K (κ → K)} {Qm : QuadraticForm K (ι → K)}
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x))
    (hker : ∀ z, R *ᵥ z = 0 → (∀ x, R *ᵥ x = 0 → polar Qg z x = 0) → z = 0)
    (hndg : Qg.polarBilin.Nondegenerate) (hndm : Qm.polarBilin.Nondegenerate)
    (hTm : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Qm x = 0)
    {A : GL κ K} (hA : A ∈ StatedOmega ⇑Qg)
    (hfix : ∀ x, R *ᵥ x = 0 → (A : Matrix κ κ K) *ᵥ x = x) :
    ∃ h : GL ι K, h ∈ StatedOmega ⇑Qm ∧ pcExtMat M R (h : Matrix ι ι K) = A := by
  have hAiso := pd_isometry_of_mem_statedOmega hA
  have hAinv : A⁻¹ ∈ StatedOmega ⇑Qg := inv_mem hA
  have hfixinv : ∀ x, R *ᵥ x = 0 → ((A⁻¹ : GL κ K) : Matrix κ κ K) *ᵥ x = x := by
    intro x hx
    conv_lhs => rw [← hfix x hx]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨hAM, hA1⟩ := pcExtMat_eq_of_fix hRM hQ hker hAiso hfix
  obtain ⟨-, hA2⟩ := pcExtMat_eq_of_fix hRM hQ hker (pd_isometry_of_mem_statedOmega hAinv)
    hfixinv
  set H := R * (A : Matrix κ κ K) * M with hH
  set H' := R * ((A⁻¹ : GL κ K) : Matrix κ κ K) * M with hH'
  have hHH' : H * H' = 1 := by
    apply pcExtMat_injective hRM
    rw [pcExtMat_mul hRM, ← hA1, ← hA2, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      pcExtMat_one]
  have hH'H : H' * H = 1 := by
    apply pcExtMat_injective hRM
    rw [pcExtMat_mul hRM, ← hA1, ← hA2, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      pcExtMat_one]
  set h0 : GL ι K := ⟨H, H', hHH', hH'H⟩ with hh0
  have hQM : ∀ y, Qg (M *ᵥ y) = Qm y := fun y => by
    have h1 := hQ 0 y
    simpa using h1
  have hiso : ∀ y, Qm ((h0 : Matrix ι ι K) *ᵥ y) = Qm y := fun y => by
    change Qm (H *ᵥ y) = Qm y
    rw [← hQM, ← hAM, hAiso, hQM]
  have hev : Even (((h0 : Matrix ι ι K) - 1).rank) := by
    have h1 := pdEven_rank_of_mem_statedOmega Qg hndg hA
    have h2 : (A : Matrix κ κ K) - 1 = M * (H - 1) * R := by
      conv_lhs => rw [hA1]
      rw [pcExtMat, add_sub_cancel_left]
    rw [h2, pd_rank_conj hRM] at h1
    exact h1
  exact ⟨h0, pdMem_statedOmega_of_even Qm hndm hTm hiso hev, hA1.symm⟩

end Ext

end CFSG.SeitzReduction.SymplecticPilot
