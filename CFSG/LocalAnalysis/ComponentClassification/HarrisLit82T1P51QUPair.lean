module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUEig

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n m : ℕ}

theorem gramForm_one_mulVec_mulVec (A C : Matrix (Fin m) (Fin m) K) (x y : Fin m → K) :
    gramForm h 1 (A *ᵥ x) (C *ᵥ y) = gramForm h 1 x (((A.map h.bar)ᵀ * C) *ᵥ y) := by
  rw [gramForm_apply, gramForm_apply, one_mulVec, one_mulVec]
  have hx : (fun a => h.bar ((A *ᵥ x) a)) = A.map h.bar *ᵥ fun a => h.bar (x a) := by
    funext a
    simp [mulVec, dotProduct, map_sum]
  rw [hx, ← vecMul_transpose (A.map h.bar), ← dotProduct_mulVec, mulVec_mulVec]

@[expose] def adjInv : GL (Fin m) K →* GL (Fin m) K where
  toFun x := ⟨(((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ,
    ((x : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ,
    by rw [← transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one],
    by rw [← transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]⟩
  map_one' := Units.ext (by simp [Matrix.map_one _ (map_zero h.bar) (map_one h.bar)])
  map_mul' x y := Units.ext (by simp [_root_.mul_inv_rev, Matrix.map_mul, transpose_mul])

theorem coe_adjInv (x : GL (Fin m) K) : (adjInv h x : Matrix (Fin m) (Fin m) K) =
    (((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ := rfl

theorem conjTranspose_mul_adjInv (x : GL (Fin m) K) :
    ((x : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * (adjInv h x : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [coe_adjInv, ← transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]

theorem conjTranspose_adjInv_mul (x : GL (Fin m) K) :
    (((adjInv h x : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ *
      (x : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [coe_adjInv, Matrix.transpose_map, transpose_transpose]
  have h1 : (((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map h.bar).map h.bar =
      ((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    ext i j
    simp [UnitaryFieldData.bar_bar]
  rw [h1, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem det_adjInv {x : GL (Fin m) K} (hx : (x : Matrix (Fin m) (Fin m) K).det = 1) :
    (adjInv h x : Matrix (Fin m) (Fin m) K).det = 1 := by
  have h1 := congrArg det (conjTranspose_mul_adjInv h x)
  have h2 : ((x : Matrix (Fin m) (Fin m) K).map h.bar).det =
      h.bar (x : Matrix (Fin m) (Fin m) K).det := by
    rw [RingHom.map_det]
    rfl
  rw [det_mul, det_transpose, det_one, h2, hx, map_one, one_mul] at h1
  exact h1

theorem exists_paired_unitary_coord (hp2 : p ≠ 2) (a : gramSU h (idGram K n)) {l : K}
    (hl0 : l ≠ 0) (hAA : unitaryOp (suOp h a) * unitaryOp (suOp h a) = (l ^ 2) • 1)
    (hlN : h.norm l = -1) :
    ∃ (hc : IsCompl (eigP l (unitaryOp (suOp h a))) (eigM l (unitaryOp (suOp h a))))
      (eP : eigP l (unitaryOp (suOp h a)) ≃ₗ[K]
        (Fin (finrank K (eigP l (unitaryOp (suOp h a)))) → K))
      (eM : eigM l (unitaryOp (suOp h a)) ≃ₗ[K]
        (Fin (finrank K (eigP l (unitaryOp (suOp h a)))) → K)),
      ∀ v w, gramForm h 1 v w =
        gramForm h 1 (eigCoord hc eP eM v).1 (eigCoord hc eP eM w).2 +
          gramForm h 1 (eigCoord hc eP eM v).2 (eigCoord hc eP eM w).1 := by
  have htwo := two_ne_zero_of_odd h hp2
  set A := unitaryOp (suOp h a)
  have hc : IsCompl (eigP l A) (eigM l A) :=
    isCompl_ker_sub_one_ker_add_one htwo (invSMulOp_mul_self hl0 hAA)
  set B := idForm h n
  have hT : ∀ v w, B (invSMulOp l A v) (invSMulOp l A w) = -B v w := fun v w => by
    rw [sesq_invSMulOp l (suOp h a) v w, hlN]
    ring
  have hisoP : ∀ v ∈ eigP l A, ∀ w ∈ eigP l A, B v w = 0 :=
    fun v hv w hw => sesq_eq_zero_of_eigen_neg_plus htwo hT hv hw
  have hisoM : ∀ v ∈ eigM l A, ∀ w ∈ eigM l A, B v w = 0 :=
    fun v hv w hw => sesq_eq_zero_of_eigen_neg_minus htwo hT hv hw
  have hsym : ∀ v w, B v w = h.bar (B w v) := fun v w => ((idForm_isSymm h n).eq w v).symm
  have hpairP : ∀ v ∈ eigP l A, (∀ w ∈ eigM l A, B v w = 0) → v = 0 := by
    intro v hv hvw
    refine idForm_separatingLeft h n v fun w => ?_
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
    rw [map_add, hisoP v hv x hx, hvw y hy, add_zero]
  have hpairM : ∀ w ∈ eigM l A, (∀ v ∈ eigP l A, B w v = 0) → w = 0 := by
    intro w hw hwv
    refine idForm_separatingLeft h n w fun u => ?_
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint u
    rw [map_add, hwv x hx, hisoM w hw y hy, add_zero]
  have hdim : finrank K (eigM l A) = finrank K (eigP l A) :=
    le_antisymm (finrank_le_of_pairing hpairM) (finrank_le_of_pairing hpairP)
  set bP := Module.finBasis K (eigP l A)
  set Λ : eigM l A →ₗ[K] (Fin (finrank K (eigP l A)) → K) :=
    { toFun := fun w i => B (bP i) w
      map_add' := fun w w' => funext fun i => by simp
      map_smul' := fun c w => funext fun i => by simp }
  have hΛ : ∀ w i, Λ w i = B (bP i) w := fun _ _ => rfl
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine Subtype.ext (hpairM w w.2 fun v hv => ?_)
    rw [hsym]
    have h1 : B v w = 0 := by
      have hv' : ((∑ i, bP.equivFun ⟨v, hv⟩ i • bP i : eigP l A) : Fin n → K) = v :=
        congrArg Subtype.val (bP.sum_equivFun ⟨v, hv⟩)
      rw [← hv']
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, LinearMap.map_smulₛₗ,
        LinearMap.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have := congrFun hw i
      rw [hΛ, Pi.zero_apply] at this
      rw [this, smul_zero]
    rw [h1, map_zero]
  have hsurj : Function.Surjective Λ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Module.finrank_fin_fun, hdim])).mp hinj
  refine ⟨hc, bP.equivFun, LinearEquiv.ofBijective Λ ⟨hinj, hsurj⟩, fun v w => ?_⟩
  set β := eigCoord hc bP.equivFun (LinearEquiv.ofBijective Λ ⟨hinj, hsurj⟩)
  obtain ⟨x, rfl⟩ := β.symm.surjective v
  obtain ⟨y, rfl⟩ := β.symm.surjective w
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, eigCoord_symm,
    eigCoord_symm]
  change B _ _ = _
  simp only [map_add, LinearMap.add_apply]
  rw [hisoP _ (bP.equivFun.symm x.1).2 _ (bP.equivFun.symm y.1).2,
    hisoM _ ((LinearEquiv.ofBijective Λ ⟨hinj, hsurj⟩).symm x.2).2 _
      ((LinearEquiv.ofBijective Λ ⟨hinj, hsurj⟩).symm y.2).2, zero_add, add_zero]
  have hpair : ∀ (u : Fin (finrank K (eigP l A)) → K) (z : eigM l A),
      B (bP.equivFun.symm u : Fin n → K) (z : Fin n → K) = gramForm h 1 u (Λ z) := by
    intro u z
    rw [Basis.equivFun_symm_apply, Submodule.coe_sum, map_sum, LinearMap.sum_apply,
      gramForm_apply, one_mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hΛ]
  have h1 := hpair x.1 ((LinearEquiv.ofBijective Λ ⟨hinj, hsurj⟩).symm y.2)
  have h2 := hpair y.1 ((LinearEquiv.ofBijective Λ ⟨hinj, hsurj⟩).symm x.2)
  have hΛs : ∀ z, Λ ((LinearEquiv.ofBijective Λ ⟨hinj, hsurj⟩).symm z) = z := fun z =>
    (LinearEquiv.ofBijective Λ ⟨hinj, hsurj⟩).apply_symm_apply z
  rw [hΛs] at h1 h2
  have h3 : h.bar (gramForm h 1 y.1 x.2) = gramForm h 1 x.2 y.1 := by
    rw [gramForm_apply, gramForm_apply, one_mulVec, one_mulVec, dotProduct, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, UnitaryFieldData.bar_bar, mul_comm]
  rw [h1, hsym, h2, h3, add_comm]

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
