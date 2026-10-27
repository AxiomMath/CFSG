module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal

open Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CatalogueBOrthogonalSemilinear
  CatalogueBOrthogonalInvolutionRepresentation CatalogueBOrthogonalPointData
  CatalogueBOrthogonalDescent CatalogueBLinearTwoDescent CatalogueBHigherLinearField
open CLSFourGroupScalarSquare FixedFourGroup FourGroupOddBilinear
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Commutant

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def commutant (τ : V ≃+ V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x, g (τ x) = τ (g x)}
  one_mem' _ := rfl
  mul_mem' {g h} hg hh x := by
    change g (h (τ x)) = τ (g (h x))
    rw [hh, hg]
  inv_mem' {g} hg x := by
    apply g.injective
    change g (g.symm (τ x)) = g (τ (g.symm x))
    rw [hg, g.apply_symm_apply, g.apply_symm_apply]

theorem mem_commutant {τ : V ≃+ V} {g : V ≃ₗ[K] V} :
    g ∈ commutant τ ↔ ∀ x, g (τ x) = τ (g x) :=
  Iff.rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem signEquiv_apply_basis (c : Basis ι K V) (S : Finset ι) (i : ι) :
    signEquiv c S (c i) = (if i ∈ S then -1 else 1 : K) • c i := by
  rw [← LinearEquiv.coe_coe, coe_signEquiv, Matrix.toLin_self, Finset.sum_eq_single i]
  · simp [signDiag_apply]
  · intro j _ hji
    simp [signDiag_apply, hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem signEquiv_mem_commutant {σ : K ≃+* K} {τ : V ≃+ V}
    (hτ : ∀ (a : K) x, τ (a • x) = σ a • τ x) (c : Basis ι K V) (hc : ∀ i, τ (c i) = c i)
    (S : Finset ι) : signEquiv c S ∈ commutant τ := mem_commutant.2 fun x => by
  have hε : ∀ i, σ (if i ∈ S then -1 else 1 : K) = (if i ∈ S then -1 else 1 : K) := fun i => by
    split_ifs <;> simp
  conv_lhs => rw [← c.sum_repr x]
  conv_rhs => rw [← c.sum_repr x]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hτ, hc, map_smul, signEquiv_apply_basis, smul_smul, map_mul, hε]

end Commutant

section Diagonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_four_of_diagonal_le [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {C : Subgroup (V ≃ₗ[K] V)}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : Basis ι K V) (h5 : 5 ≤ Fintype.card ι)
    (hB : ∀ i j, Q.polarBilin (c i) (c j) ≠ 0 → i = j) (hC : ∀ S, signEquiv c S ∈ C) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ (C.subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  let x : Fin 5 ↪ ι := (Fin.castLEEmb h5).trans (Fintype.equivFin ι).symm.toEmbedding
  have hx : ∀ a b : Fin 5, x a = x b ↔ a = b := fun a b => x.injective.eq_iff
  have hSO : ∀ k : Fin 5, k ≠ 0 →
      signEquiv c {x 0, x k} ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q := fun k hk =>
    TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.2
      ⟨(TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar (IsSMulRegular.of_ne_zero h2)).2
        fun v w => signEquiv_preserves Q.polarBilin c (fun i j h => by rw [hB i j h]) v w,
        Units.ext (by
          rw [det_signEquiv, Finset.card_pair (by rw [Ne, hx]; exact hk.symm),
            even_two.neg_one_pow]
          rfl)⟩
  refine exists_four_of_signSystem_le hK hQ (signEquiv c) (signEquiv_empty c) (signEquiv_mul c)
    (fun S i hi j hj => notScalar_signEquiv h2 c hi hj) (hSO 1 (by decide)) (hSO 2 (by decide))
    (hSO 3 (by decide)) (hC _) (hC _) (hC _) (z := x 4) ?_ ?_ ?_ (y₁ := x 0) (y₂ := x 0)
    (y₃ := x 0) (y₁₂ := x 1) (y₁₃ := x 1) (y₂₃ := x 2) (y₁₂₃ := x 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [Finset.mem_symmDiff, hx]

end Diagonal

section Bridge

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

omit Q in
theorem matrixLinearEquiv_scalar (c : Kˣ) (v : Fin d → K) :
    matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) c) v = (c : K) • v := by
  rw [matrixLinearEquiv_apply]
  funext i
  simp [GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]

theorem map_matrixDerived :
    (matrixDerived Q).map matrixLinearIso.toMonoidHom = orthogonalOmega Q := by
  rw [matrixDerived, Subgroup.map_commutator, matrixIsometries,
    Subgroup.map_comap_eq_self_of_surjective (f := matrixLinearIso.toMonoidHom)
      matrixLinearIso.surjective]

@[expose] def derivedEquiv : matrixDerived Q ≃* orthogonalOmega Q :=
  (matrixLinearIso.subgroupMap (matrixDerived Q)).trans
    (MulEquiv.subgroupCongr (map_matrixDerived Q))

theorem derivedEquiv_val (X : matrixDerived Q) :
    ((derivedEquiv Q X : orthogonalOmega Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearEquiv X.val :=
  rfl

theorem matrixLinearEquiv_derivedEquiv_symm (u : orthogonalOmega Q) :
    matrixLinearEquiv ((derivedEquiv Q).symm u).val = u := by
  rw [← derivedEquiv_val, MulEquiv.apply_symm_apply]

theorem map_matrixDerivedScalars (hd : 0 < d) :
    (matrixDerivedScalars Q).map (derivedEquiv Q).toMonoidHom = omegaScalars Q := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_matrixDerivedScalars_iff, mem_omegaScalars]
  have h1 := matrixLinearEquiv_derivedEquiv_symm Q h
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, LinearMap.ext fun v => ?_⟩
    rw [← h1, ← hc]
    exact matrixLinearEquiv_scalar c v
  · rintro ⟨c, hc⟩
    have hv : ∀ v, (h : (Fin d → K) ≃ₗ[K] (Fin d → K)) v = c • v := fun v =>
      LinearMap.congr_fun hc v
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h0 := hv (Pi.single ⟨0, hd⟩ 1)
      rw [zero_smul, LinearEquiv.map_eq_zero_iff] at h0
      simpa using congrFun h0 ⟨0, hd⟩
    refine ⟨Units.mk0 c hc0, matrixLinearIso.injective (LinearEquiv.ext fun v => ?_)⟩
    change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0)) v =
      matrixLinearEquiv ((derivedEquiv Q).symm h).val v
    rw [h1, hv]
    exact matrixLinearEquiv_scalar _ v

@[expose] def projEquiv (hd : 0 < d) : matrixProjectiveDerived Q ≃* OrthogonalProj Q :=
  QuotientGroup.congr (matrixDerivedScalars Q) (omegaScalars Q) (derivedEquiv Q)
    (map_matrixDerivedScalars Q hd)

theorem projEquiv_proj (hd : 0 < d) (X : matrixDerived Q) :
    projEquiv Q hd (matrixProjectiveProjection Q X) = orthogonalProj Q (derivedEquiv Q X) :=
  QuotientGroup.congr_mk' _ _ _ _ X

theorem projEquiv_symm_proj (hd : 0 < d) (u : orthogonalOmega Q) :
    (projEquiv Q hd).symm (orthogonalProj Q u) =
      matrixProjectiveProjection Q ((derivedEquiv Q).symm u) := by
  rw [MulEquiv.symm_apply_eq, projEquiv_proj, MulEquiv.apply_symm_apply]

theorem map_le_fixed (hd : 0 < d) (g : similarityPairs Q)
    {C : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    (hC : ∀ u ∈ C, ∀ v, u (coordinateSemilinearMap g.val v) = coordinateSemilinearMap g.val (u v))
    {W : Subgroup (OrthogonalProj Q)}
    (hW : W ≤ (C.subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q)) :
    W.map (projEquiv Q hd).symm.toMonoidHom ≤
      fixedSubgroup (matrixProjectiveConjugationHom Q g) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨u, hu, rfl⟩ := hW hw
  change matrixProjectiveConjugation Q g ((projEquiv Q hd).symm (orthogonalProj Q u)) =
    (projEquiv Q hd).symm (orthogonalProj Q u)
  rw [projEquiv_symm_proj, matrixProjectiveConjugation_mk]
  refine congrArg _ (Subtype.ext (matrixLinearIso.injective (LinearEquiv.ext fun v => ?_)))
  change matrixLinearEquiv (matrixConjugation g.val ((derivedEquiv Q).symm u).val) v =
    matrixLinearEquiv ((derivedEquiv Q).symm u).val v
  rw [matrixConjugation_vector, matrixLinearEquiv_derivedEquiv_symm,
    ← hC _ (Subgroup.mem_subgroupOf.1 hu), AddEquiv.apply_symm_apply]

end Bridge

theorem isSymm_polarBilin {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : LinearMap.BilinForm.IsSymm Q.polarBilin :=
  ⟨fun x y => QuadraticMap.polar_comm Q x y⟩

section Cases

variable {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {d : ℕ} (hd : 7 ≤ d)
  (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
include hK hd hQ

theorem exists_four_coordinate :
    ∃ V : Subgroup (matrixProjectiveDerived Q), CFSG.IsElementaryAbelian 2 V ∧
      Nat.card V = 4 := by
  have : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hK)
  obtain ⟨c, hc⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 (isSymm_polarBilin Q))
  obtain ⟨W, -, hab, hcard⟩ := exists_four_of_diagonal_le hK hQ (C := ⊤) c
    (by rw [Fintype.card_fin, Module.finrank_fin_fun]; omega)
    (fun i j h => by_contra fun hij => h (hc hij)) (fun _ => Subgroup.mem_top _)
  refine ⟨W.map (projEquiv Q (by omega)).symm.toMonoidHom, hab.map _, ?_⟩
  rw [Subgroup.card_map_of_injective (f := (projEquiv Q (by omega)).symm.toMonoidHom)
    (projEquiv Q (by omega)).symm.injective]
  exact hcard

theorem exists_four_linear_coordinate (g : similarityPairs Q) (hg1 : g.val.right = 1) (c : Kˣ)
    (hc : g.val.left * glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c)
    (hns : ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left) :
    ∃ V : Subgroup (matrixProjectiveDerived Q),
      V ≤ fixedSubgroup (matrixProjectiveConjugationHom Q g) ∧ CFSG.IsElementaryAbelian 2 V ∧
        Nat.card V = 4 := by
  have hd0 : 0 < d := by omega
  set A := matrixLinearEquiv g.val.left with hAdef
  have hτ : ∀ v, coordinateSemilinearMap g.val v = A v := fun v => by
    rw [coordinateSemilinearMap_apply, hg1]
    rfl
  rw [hg1, map_one] at hc
  have hsq : ∀ x, A (A x) = (c : K) • x := fun x => by
    have h1 : A (A x) = matrixLinearEquiv (g.val.left * g.val.left) x := by
      rw [matrixLinearEquiv_mul]
      rfl
    rw [h1, show g.val.left * g.val.left = GeneralLinearGroup.scalar (Fin d) c from hc]
    exact matrixLinearEquiv_scalar c x
  have hQA : ∀ v, Q (A v) = (multiplier Q g : K) * Q v := fun v => by
    rw [← hτ, multiplier_spec, hg1]
    rfl
  have hsim : ∀ x y, Q.polarBilin (A x) (A y) = (multiplier Q g : K) * Q.polarBilin x y := by
    intro x y
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar, ← map_add A x y, hQA,
      hQA, hQA]
    ring
  have hAns : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K (Fin d → K)) := fun a h => by
    have hv : ∀ v, A v = a • v := fun v => LinearMap.congr_fun h v
    have ha : a ≠ 0 := by
      rintro rfl
      have h0 := hv (Pi.single ⟨0, hd0⟩ 1)
      rw [zero_smul, LinearEquiv.map_eq_zero_iff] at h0
      simpa using congrFun h0 ⟨0, hd0⟩
    refine hns (Units.mk0 a ha) (matrixLinearIso.injective (LinearEquiv.ext fun v => ?_))
    change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (Units.mk0 a ha)) v = A v
    rw [hv]
    exact matrixLinearEquiv_scalar _ v
  obtain ⟨W, hW, hab, hcard⟩ := odd_orthogonal_scalar_square_centralizer_projective_four_group hK
    (by rw [Module.finrank_fin_fun]; exact hd) Q hQ A c (multiplier Q g) hsq hsim hAns
  refine ⟨W.map (projEquiv Q hd0).symm.toMonoidHom, map_le_fixed Q hd0 g (fun u hu v => ?_) hW,
    hab.map _, ?_⟩
  · rw [hτ, hτ]
    exact LinearEquiv.congr_fun (Subgroup.mem_centralizer_singleton_iff.1 hu) v
  · rw [Subgroup.card_map_of_injective (f := (projEquiv Q hd0).symm.toMonoidHom)
      (projEquiv Q hd0).symm.injective]
    exact hcard

theorem exists_four_semilinear_coordinate (g : similarityPairs Q) (hg2 : g.val.right ^ 2 = 1)
    (hg1 : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c) :
    ∃ V : Subgroup (matrixProjectiveDerived Q),
      V ≤ fixedSubgroup (matrixProjectiveConjugationHom Q g) ∧ CFSG.IsElementaryAbelian 2 V ∧
        Nat.card V = 4 := by
  have hd0 : 0 < d := by omega
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hsemi : ∀ (a : K) x, coordinateSemilinearMap g.val (a • x) =
      g.val.right a • coordinateSemilinearMap g.val x := coordinateSemilinearMap_smul g.val
  have hQτ := multiplier_spec Q g
  have hform : ∀ x y, Q.polarBilin (coordinateSemilinearMap g.val x)
      (coordinateSemilinearMap g.val y) =
        (multiplier Q g : K) * g.val.right (Q.polarBilin x y) := by
    intro x y
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar,
      ← map_add (coordinateSemilinearMap g.val) x y, hQτ, hQτ, hQτ, map_sub, map_sub]
    ring
  have hsquare : ∀ x, coordinateSemilinearMap g.val (coordinateSemilinearMap g.val x) =
      (c : K) • x := fun x => by
    rw [← coordinateSemilinearMap_mul, coordinateSemilinearMap_apply,
      coordinateSemilinearGroup_mul_matrix, hc, coordinateSemilinearGroup_mul_field, ← pow_two, hg2]
    exact matrixLinearEquiv_scalar c x
  obtain ⟨-, -, -, ⟨b, c', hb, hc'⟩, hall⟩ := odd_orthogonal_quadratic_semilinear_descent
    g.val.right hg2 hg1 h2 (by rw [Module.finrank_fin_fun]; exact hd0) Q.polarBilin
    (isSymm_polarBilin Q) hQ (coordinateSemilinearMap g.val) (multiplier Q g) c hsemi
    hform hsquare
  obtain ⟨-, hTapply, hTsemi, hW, hfin, hrank, hB0sym, -, hB0apply, -, -, -, j, -, hj, -⟩ :=
    hall b c' hb hc'
  have h2k : (2 : fixedSubfield K g.val.right) ≠ 0 := fun h => by
    have h3 := map_ofNat (fixedSubfield K g.val.right).subtype 2
    rw [h, map_zero] at h3
    exact h2 h3.symm
  have : Invertible (2 : fixedSubfield K g.val.right) := invertibleOfNonzero h2k
  obtain ⟨bW, hbW⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 hB0sym)
  let cV := (Algebra.TensorProduct.basis K bW).map j
  have hcV : ∀ i, cV i = (bW i : Fin d → K) := fun i => by
    simp only [cV, Basis.map_apply, Algebra.TensorProduct.basis_apply, hj, one_smul]
  have hT : ∀ i, normalizedOperator (coordinateSemilinearMap g.val) b (cV i) = cV i := fun i => by
    rw [hTapply, hcV]
    exact (hW _).1 (bW i).2
  have hB : ∀ i j, Q.polarBilin (cV i) (cV j) ≠ 0 → i = j := fun i i' h => by
    by_contra hii
    apply h
    have h0 : (c' : K) * Q.polarBilin (bW i : Fin d → K) (bW i') = 0 := by
      rw [← hB0apply, show _ = (0 : fixedSubfield K g.val.right) from hbW hii]
      rfl
    rw [hcV, hcV]
    exact (mul_eq_zero.1 h0).resolve_left (Units.ne_zero c')
  have hC : ∀ S, signEquiv cV S ∈ commutant (coordinateSemilinearMap g.val) := fun S =>
    mem_commutant.2 fun x => by
      have hx := mem_commutant.1 (signEquiv_mem_commutant hTsemi cV hT S) x
      rw [hTapply, hTapply, map_smul] at hx
      exact smul_right_injective _ (Units.ne_zero b) hx
  obtain ⟨W, hWle, hab, hcard⟩ := exists_four_of_diagonal_le hK hQ cV
    (by rw [Fintype.card_fin, hrank, Module.finrank_fin_fun]; omega) hB hC
  refine ⟨W.map (projEquiv Q hd0).symm.toMonoidHom,
    map_le_fixed Q hd0 g (fun u hu v => mem_commutant.1 hu v) hWle, hab.map _, ?_⟩
  rw [Subgroup.card_map_of_injective (f := (projEquiv Q hd0).symm.toMonoidHom)
    (projEquiv Q hd0).symm.injective]
  exact hcard

end Cases

theorem exists_fixed_four_group_coordinate {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) {d : ℕ} (hd : 7 ≤ d) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (hrep : SemilinearRepresentation Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : α * α = 1) :
    ∃ V : Subgroup (matrixProjectiveDerived Q), V ≤ fixedSubgroup α ∧
      CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  by_cases h1 : α = 1
  · subst h1
    obtain ⟨V, hab, hcard⟩ := exists_four_coordinate hK hd Q hQ
    exact ⟨V, fun v _ => rfl, hab, hcard⟩
  · obtain ⟨β, g, hβ, hg2, ⟨c, hc⟩, hlin, -⟩ := hrep.2 α hα h1
    obtain ⟨V, hV, hab, hcard⟩ :
        ∃ V : Subgroup (matrixProjectiveDerived Q),
          V ≤ fixedSubgroup (matrixProjectiveConjugationHom Q g) ∧
            CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
      by_cases hg1 : g.val.right = 1
      · exact exists_four_linear_coordinate hK hd Q hQ g hg1 c hc (hlin hg1)
      · exact exists_four_semilinear_coordinate hK hd Q hQ g hg2 hg1 c hc
    refine exists_four_group_le_fixedSubgroup_of_congr β⁻¹ α ?_ hab hcard
    rw [congr_eq_conj, inv_inv, hβ]
    exact hV

theorem odd_orthogonal_all_involution_fixed_four_group (L : Type) [Group L] {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ} (hp : p ≠ 2)
    (hL : StatedClassicalModel L t n p f) (α : MulAut L) (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  have hrep := odd_orthogonal_involution_semilinear_representation t ht hL
  have finish : ∀ {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)),
      ringChar K = p → 7 ≤ d → Q.polarBilin.Nondegenerate → SemilinearRepresentation Q →
      (L ≃* matrixProjectiveDerived Q) →
      ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ CFSG.IsElementaryAbelian 2 V ∧
        Nat.card V = 4 := by
    intro K _ _ d Q hchar hd hQ hrepQ ψ
    obtain ⟨V, hV, hab, hcard⟩ := exists_fixed_four_group_coordinate (by rw [hchar]; exact hp)
      hd Q hQ hrepQ (MulAut.congr ψ α) (by rw [← map_mul, ← pow_two, hα, map_one])
    exact exists_four_group_le_fixedSubgroup_of_congr ψ α hV hab hcard
  rcases ht with rfl | rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL.2
    obtain ⟨hchar, hQ, -⟩ := coordinate_model_witness_odd hL K hK e
    exact finish _ hchar (by have := hL.1.2.2.1; omega) hQ (hrep K hK e)
      (coordinateOddWitnessEquiv K e)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL.2
    obtain ⟨hchar, hQ, -⟩ := coordinate_model_witness_plus hL K hK e
    exact finish _ hchar (by have := hL.1.2.2; omega) hQ (hrep K hK e)
      (coordinatePlusWitnessEquiv K e)
  · obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hL.2
    have hn : 1 ≤ n := by have := hL.1.2.2; omega
    obtain ⟨hchar, hQ, -⟩ := coordinate_model_witness_minus hL K hK b c hirr e
    exact finish _ hchar (by have := hL.1.2.2; omega) hQ (hrep hn K hK b c hirr e)
      (coordinateMinusWitnessEquiv K hn b c e)

theorem odd_orthogonal_all_involution_fixed_four_group_of_classicalModel (L : Type) [Group L]
    {t : CFSG.Assembly.ComponentType.ClassicalTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hL : CFSG.Assembly.ComponentType.ClassicalModel L t n p f) (α : MulAut L)
    (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 :=
  odd_orthogonal_all_involution_fixed_four_group L
    (by rcases ht with rfl | rfl | rfl
        exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)])
    hp (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel t n p f hL) α hα

end CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal
