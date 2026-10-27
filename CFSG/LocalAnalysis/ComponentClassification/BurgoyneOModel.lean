module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProj
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
variable {K : Type} [Field K] {d : ℕ}

theorem commute_scalar (c : Kˣ) (g : GL (Fin d) K) :
    Commute g (GeneralLinearGroup.scalar (Fin d) c) := by
  apply Units.ext
  change (g : Matrix (Fin d) (Fin d) K) * Matrix.scalar (Fin d) (c : K) =
    Matrix.scalar (Fin d) (c : K) * g
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul]

abbrev oQ (R : GL (Fin d) K) : QuadraticForm K (Fin d → K) :=
  CatalogueBLinearHigherB.matrixQuadraticForm R

theorem oQ_apply (R : GL (Fin d) K) (v : Fin d → K) :
    oQ R v = v ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ v :=
  CatalogueBLinearHigherB.matrixForm_apply R v v

theorem eq_of_forall_dotProduct_mulVec (h2 : (2 : K) ≠ 0) {M N : Matrix (Fin d) (Fin d) K}
    (hM : Mᵀ = M) (hN : Nᵀ = N) (h : ∀ v, v ⬝ᵥ M *ᵥ v = v ⬝ᵥ N *ᵥ v) : M = N := by
  have hdiag : ∀ i, M i i = N i i := by
    intro i
    have := h (Pi.single i 1)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  ext i j
  by_cases hij : i = j
  · rw [hij, hdiag]
  have hMs : M j i = M i j := by rw [← transpose_apply M i j, hM]
  have hNs : N j i = N i j := by rw [← transpose_apply N i j, hN]
  have e := h (Pi.single i 1 + Pi.single j 1)
  simp only [mulVec_add, mulVec_single_one, dotProduct_add, add_dotProduct,
    single_one_dotProduct, col_apply] at e
  rw [hMs, hNs, hdiag i, hdiag j] at e
  have : (2 : K) * (M i j - N i j) = 0 := by linear_combination e
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2)

theorem mem_matrixIsometries_oQ (h2 : (2 : K) ≠ 0) (R : GL (Fin d) K)
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (X : GL (Fin d) K) :
    X ∈ matrixIsometries (oQ R) ↔ X ∈ CatalogueBGraphForm.isometryGroup d K R := by
  rw [mem_matrixIsometries_iff, CatalogueBGraphForm.mem_isometryGroup]
  have key : ∀ v, oQ R (matrixLinearEquiv X v) =
      v ⬝ᵥ ((X : Matrix (Fin d) (Fin d) K)ᵀ * (R : Matrix (Fin d) (Fin d) K) *
        (X : Matrix (Fin d) (Fin d) K)) *ᵥ v := by
    intro v
    have e1 : v ⬝ᵥ ((X : Matrix (Fin d) (Fin d) K)ᵀ * (R : Matrix (Fin d) (Fin d) K) *
        (X : Matrix (Fin d) (Fin d) K)) *ᵥ v = ((X : Matrix (Fin d) (Fin d) K) *ᵥ v) ⬝ᵥ
          (R : Matrix (Fin d) (Fin d) K) *ᵥ ((X : Matrix (Fin d) (Fin d) K) *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        vecMul_transpose]
    rw [oQ_apply, matrixLinearEquiv_apply, e1]
  constructor
  · intro hX
    refine eq_of_forall_dotProduct_mulVec h2 ?_ hR fun v => ?_
    · rw [transpose_mul, transpose_mul, transpose_transpose, hR, Matrix.mul_assoc]
    · rw [← key, hX v, oQ_apply]
  · intro hX v
    rw [key, hX, oQ_apply]

theorem matrixIsometries_oQ (h2 : (2 : K) ≠ 0) (R : GL (Fin d) K)
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) :
    matrixIsometries (oQ R) = CatalogueBGraphForm.isometryGroup d K R :=
  Subgroup.ext (mem_matrixIsometries_oQ h2 R hR)

theorem matrixDerived_oQ (h2 : (2 : K) ≠ 0) (R : GL (Fin d) K)
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) :
    matrixDerived (oQ R) = ⁅CatalogueBGraphForm.isometryGroup d K R,
      CatalogueBGraphForm.isometryGroup d K R⁆ := by
  rw [matrixDerived, matrixIsometries_oQ h2 R hR]

theorem coe_glFieldAut (σ : K ≃+* K) (X : GL (Fin d) K) :
    ((glFieldAut (Fin d) K σ X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (X : Matrix (Fin d) (Fin d) K).map σ := rfl

theorem mem_similarityPairs_oQ (h2 : (2 : K) ≠ 0) (R : GL (Fin d) K)
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (g : coordinateSemilinearGroup d K) :
    g ∈ similarityPairs (oQ R) ↔ ∃ μ : Kˣ,
      (g.left : Matrix (Fin d) (Fin d) K)ᵀ * (R : Matrix (Fin d) (Fin d) K) *
          (g.left : Matrix (Fin d) (Fin d) K) =
        (μ : K) • (R : Matrix (Fin d) (Fin d) K).map g.right := by
  rw [mem_similarityPairs_iff]
  have hσv : ∀ v : Fin d → K, g.right (oQ R v) =
      (fun i => g.right (v i)) ⬝ᵥ ((R : Matrix (Fin d) (Fin d) K).map g.right) *ᵥ
        (fun i => g.right (v i)) := by
    intro v
    rw [oQ_apply]
    simp only [dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]
  have hL : ∀ v : Fin d → K, oQ R (coordinateSemilinearMap g v) =
      (fun i => g.right (v i)) ⬝ᵥ ((g.left : Matrix (Fin d) (Fin d) K)ᵀ *
        (R : Matrix (Fin d) (Fin d) K) * (g.left : Matrix (Fin d) (Fin d) K)) *ᵥ
          (fun i => g.right (v i)) := by
    intro v
    set u : Fin d → K := fun i => g.right (v i) with hu
    have e1 : u ⬝ᵥ ((g.left : Matrix (Fin d) (Fin d) K)ᵀ * (R : Matrix (Fin d) (Fin d) K) *
        (g.left : Matrix (Fin d) (Fin d) K)) *ᵥ u = ((g.left : Matrix (Fin d) (Fin d) K) *ᵥ u) ⬝ᵥ
          (R : Matrix (Fin d) (Fin d) K) *ᵥ ((g.left : Matrix (Fin d) (Fin d) K) *ᵥ u) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        vecMul_transpose]
    rw [oQ_apply, coordinateSemilinearMap_apply, e1]
  have hsurj : ∀ u : Fin d → K, ∃ v : Fin d → K, (fun i => g.right (v i)) = u :=
    fun u => ⟨fun i => g.right.symm (u i), funext fun i => g.right.apply_symm_apply _⟩
  have hRσ : ((R : Matrix (Fin d) (Fin d) K).map g.right)ᵀ =
      (R : Matrix (Fin d) (Fin d) K).map g.right := by rw [← transpose_map, hR]
  constructor
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, eq_of_forall_dotProduct_mulVec h2 ?_ ?_ fun u => ?_⟩
    · rw [transpose_mul, transpose_mul, transpose_transpose, hR, Matrix.mul_assoc]
    · rw [transpose_smul, hRσ]
    · obtain ⟨v, rfl⟩ := hsurj u
      rw [← hL, hμ v, hσv, smul_mulVec, dotProduct_smul, smul_eq_mul]
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, fun v => ?_⟩
    rw [hL, hμ, hσv, smul_mulVec, dotProduct_smul, smul_eq_mul]

variable (Q : QuadraticForm K (Fin d → K))

@[expose] def oκ : similarityPairs Q →* MulAut (StatedProj (matrixDerived Q)) :=
  matrixProjectiveConjugationHom Q

theorem kappa_proj (g : similarityPairs Q) (X : matrixDerived Q) :
    oκ Q g (projH _ X) = projH _ (matrixDerivedConjugation Q g X) :=
  matrixProjectiveConjugation_mk Q g X

variable {Q} {Q' : QuadraticForm K (Fin d → K)}

theorem map_matrixIsometries_conj (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) :
    (matrixIsometries Q).map (MulAut.conj S).toMonoidHom = matrixIsometries Q' := by
  have hSi : ∀ v, Q (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) =
      (ν : K)⁻¹ * Q' v := by
    intro v
    have e := hS (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at e
    rw [e, ← mul_assoc, inv_mul_cancel₀ ν.ne_zero, one_mul]
  ext X
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rw [mem_matrixIsometries_iff] at hY ⊢
    intro v
    change Q' (((S * Y * S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) = Q' v
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hS]
    change (ν : K) * Q (matrixLinearEquiv Y _) = _
    rw [hY, hSi, ← mul_assoc, mul_inv_cancel₀ ν.ne_zero, one_mul]
  · intro hX
    refine ⟨S⁻¹ * X * S, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [mem_matrixIsometries_iff] at hX ⊢
    intro v
    change Q (((S⁻¹ * X * S : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) = Q v
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSi]
    change (ν : K)⁻¹ * Q' (matrixLinearEquiv X _) = _
    rw [hX, hS, ← mul_assoc, inv_mul_cancel₀ ν.ne_zero, one_mul]

theorem map_matrixDerived_conj (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) :
    (matrixDerived Q).map (MulAut.conj S).toMonoidHom = matrixDerived Q' := by
  rw [matrixDerived, matrixDerived, Subgroup.map_commutator, map_matrixIsometries_conj S ν hS]

theorem map_scalars_conj (S : GL (Fin d) K) :
    (StatedScalars (Fin d) K).map (MulAut.conj S).toMonoidHom = StatedScalars (Fin d) K := by
  ext X
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨c, ?_⟩
    change _ = S * _ * S⁻¹
    rw [(commute_scalar c S).eq, mul_inv_cancel_right]
  · rintro ⟨c, rfl⟩
    refine ⟨GeneralLinearGroup.scalar (Fin d) c, ⟨c, rfl⟩, ?_⟩
    change S * _ * S⁻¹ = _
    rw [(commute_scalar c S).eq, mul_inv_cancel_right]

@[expose] def derivedTransport (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) :
    matrixDerived Q ≃* matrixDerived Q' :=
  ((MulAut.conj S).subgroupMap (matrixDerived Q)).trans
    (MulEquiv.subgroupCongr (map_matrixDerived_conj S ν hS))

theorem coe_derivedTransport (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) (X : matrixDerived Q) :
    ((derivedTransport S ν hS X : matrixDerived Q') : GL (Fin d) K) = S * X * S⁻¹ := rfl

theorem map_scalars_derivedTransport (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) :
    ((StatedScalars (Fin d) K).subgroupOf (matrixDerived Q)).map
        (derivedTransport S ν hS).toMonoidHom =
      (StatedScalars (Fin d) K).subgroupOf (matrixDerived Q') := by
  ext X
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hY
    rw [← map_scalars_conj S]
    exact ⟨Y, hY, rfl⟩
  · intro hX
    obtain ⟨c, hc⟩ := hX
    have hXmem : (X : GL (Fin d) K) ∈ (matrixDerived Q).map (MulAut.conj S).toMonoidHom := by
      rw [map_matrixDerived_conj S ν hS]
      exact X.2
    obtain ⟨Z, hZ, hZX⟩ := hXmem
    have hZc : Z = (X : GL (Fin d) K) := by
      apply (MulAut.conj S).injective
      change S * Z * S⁻¹ = S * (X : GL (Fin d) K) * S⁻¹
      change S * Z * S⁻¹ = (X : GL (Fin d) K) at hZX
      rw [hZX, ← hc, (commute_scalar c S).eq, mul_inv_cancel_right]
    refine ⟨⟨Z, hZ⟩, ?_, Subtype.ext hZX⟩
    rw [Subgroup.mem_subgroupOf]
    change Z ∈ StatedScalars (Fin d) K
    rw [hZc]
    exact ⟨c, hc⟩

@[expose] def oTransport (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) :
    StatedProj (matrixDerived Q) ≃* StatedProj (matrixDerived Q') :=
  QuotientGroup.congr _ _ (derivedTransport S ν hS) (map_scalars_derivedTransport S ν hS)

theorem oTransport_proj (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) (X : matrixDerived Q) :
    oTransport S ν hS (projH _ X) = projH _ (derivedTransport S ν hS X) :=
  QuotientGroup.congr_mk' _ _ _ _ X

theorem map_mulVec_field (σ : K ≃+* K) (M : Matrix (Fin d) (Fin d) K) (v : Fin d → K) :
    M.map σ *ᵥ (fun i => σ (v i)) = fun i => σ ((M *ᵥ v) i) := by
  funext i
  simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

@[expose] def transPair (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) (g : similarityPairs Q) :
    similarityPairs Q' :=
  ⟨⟨S * g.val.left * (glFieldAut (Fin d) K g.val.right S)⁻¹, g.val.right⟩, by
    obtain ⟨μ, hμ⟩ := g.2
    refine ⟨ν * μ * (Units.map g.val.right.toMonoidHom ν)⁻¹, fun v => ?_⟩
    set σ := g.val.right with hσ
    have hSi : ∀ w, Q (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) =
        (ν : K)⁻¹ * Q' w := by
      intro w
      have e := hS (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w)
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec] at e
      rw [e, ← mul_assoc, inv_mul_cancel₀ ν.ne_zero, one_mul]
    have e1 : coordinateSemilinearMap
        (⟨S * g.val.left * (glFieldAut (Fin d) K σ S)⁻¹, σ⟩ : coordinateSemilinearGroup d K) v =
        (S : Matrix (Fin d) (Fin d) K) *ᵥ coordinateSemilinearMap g.val
          (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) := by
      rw [coordinateSemilinearMap_apply, coordinateSemilinearMap_apply, ← map_inv,
        Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        coe_glFieldAut, map_mulVec_field]
    rw [e1, hS, hμ, hSi, map_mul, map_inv₀, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.coe_map]
    change _ = (ν : K) * μ * (σ (ν : K))⁻¹ * σ (Q' v)
    ring⟩

theorem transPair_left (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) (g : similarityPairs Q) :
    (transPair S ν hS g).val.left = S * g.val.left * (glFieldAut (Fin d) K g.val.right S)⁻¹ :=
  rfl

theorem transPair_right (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) (g : similarityPairs Q) :
    (transPair S ν hS g).val.right = g.val.right := rfl

theorem oTransport_kappa (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) (g : similarityPairs Q) :
    MulAut.congr (oTransport S ν hS) (oκ Q g) = oκ Q' (transPair S ν hS g) := by
  have key : ∀ x, oTransport S ν hS (oκ Q g x) =
      oκ Q' (transPair S ν hS g) (oTransport S ν hS x) := by
    intro x
    obtain ⟨X, rfl⟩ := projH_surjective x
    rw [kappa_proj, oTransport_proj, oTransport_proj, kappa_proj]
    congr 1
    apply Subtype.ext
    rw [coe_derivedTransport, matrixDerivedConjugation_val, matrixDerivedConjugation_val,
      coe_derivedTransport, transPair_left, transPair_right, map_mul, map_mul, map_inv]
    group
  refine MulEquiv.ext fun y => ?_
  exact (key _).trans (congrArg _ (MulEquiv.apply_symm_apply _ y))

variable (Q) in
@[expose] def OKer : Prop :=
  ∀ g : similarityPairs Q, oκ Q g = 1 →
    g.val.right = 1 ∧ ∃ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a = g.val.left

variable (Q) in
@[expose] def OSurj : Prop :=
  ∀ α : MulAut (StatedProj (matrixDerived Q)), ∃ g : similarityPairs Q, α = oκ Q g

theorem transPair_transPair (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v)
    (hSi : ∀ v, Q (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) = (ν⁻¹ : Kˣ) * Q' v)
    (g : similarityPairs Q') : transPair S ν hS (transPair S⁻¹ ν⁻¹ hSi g) = g := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change S * (S⁻¹ * g.val.left * (glFieldAut (Fin d) K g.val.right S⁻¹)⁻¹) *
      (glFieldAut (Fin d) K g.val.right S)⁻¹ = g.val.left
    rw [map_inv, inv_inv]
    group
  · rfl

theorem inv_similarity (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) :
    ∀ v, Q (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) = (ν⁻¹ : Kˣ) * Q' v := by
  intro w
  have e := hS (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec] at e
  rw [e, Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ ν.ne_zero, one_mul]

theorem exists_transPair_eq (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) (g' : similarityPairs Q') :
    ∃ g : similarityPairs Q, transPair S ν hS g = g' :=
  ⟨_, transPair_transPair S ν hS (inv_similarity S ν hS) g'⟩

theorem OKer.transport (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) (hQ : OKer Q) : OKer Q' := by
  intro g' hg'
  obtain ⟨g, rfl⟩ := exists_transPair_eq S ν hS g'
  rw [← oTransport_kappa] at hg'
  have hg : oκ Q g = 1 := by
    have := congrArg (MulAut.congr (oTransport S ν hS)).symm hg'
    rwa [MulEquiv.symm_apply_apply, map_one] at this
  obtain ⟨h1, a, ha⟩ := hQ g hg
  refine ⟨h1, a, ?_⟩
  rw [transPair_left, h1, map_one, MulAut.one_apply, ← ha, (commute_scalar a S).eq,
    mul_inv_cancel_right]

theorem OSurj.transport (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) (hQ : OSurj Q) :
    OSurj Q' := by
  intro α
  obtain ⟨g, hg⟩ := hQ ((MulAut.congr (oTransport S ν hS)).symm α)
  refine ⟨transPair S ν hS g, ?_⟩
  rw [← oTransport_kappa, ← hg, MulEquiv.apply_symm_apply]

theorem OKer.right_pow_eq_one (hQ : OKer Q) {g : similarityPairs Q} {m : ℕ}
    (hm : oκ Q g ^ m = 1) : g.val.right ^ m = 1 := by
  rw [← map_pow] at hm
  have h1 := (hQ _ hm).1
  have e : ((g ^ m : similarityPairs Q) : coordinateSemilinearGroup d K).right =
      g.val.right ^ m := by
    rw [SubgroupClass.coe_pow]
    exact map_pow (SemidirectProduct.rightHom (φ := glFieldAut (Fin d) K)) g.val m
  rw [← e]
  exact h1

theorem kappa_lift (g : similarityPairs Q) (X : matrixDerived Q) :
    oκ Q g (projH _ X) = projH _ ((matrixDerivedConjugation Q g).toMonoidHom X) :=
  kappa_proj _ g X

theorem kappa_eq_of_fix (g : similarityPairs Q) {F : Subgroup (matrixDerived Q)} (hF : ⁅F, F⁆ = F)
    (hfix : ∀ X ∈ F, oκ Q g (projH _ X) = projH _ X) {X : matrixDerived Q} (hX : X ∈ F) :
    (g.val.left : Matrix (Fin d) (Fin d) K) *
        ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map g.val.right *
        ((g.val.left⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have h1 := lift_eq_of_commutator_eq (matrixDerivedConjugation Q g).toMonoidHom
    (kappa_lift g) hF hfix hX
  have h2 := congrArg (fun Y : matrixDerived Q => ((Y : GL (Fin d) K) :
    Matrix (Fin d) (Fin d) K)) h1
  simp only [MulEquiv.coe_toMonoidHom, matrixDerivedConjugation_val, Units.val_mul,
    coe_glFieldAut] at h2
  exact h2

end CFSG.ComponentClassification.Burgoyne.O
