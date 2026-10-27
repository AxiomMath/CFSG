module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Semilinear

variable {K U : Type*} [Field K] [AddCommGroup U] [Module K U]

theorem linearIndependent_semilinear (σ : K ≃+* K) (τ : U ≃+ U)
    (hτ : ∀ (a : K) (u : U), τ (a • u) = σ a • τ u) {ι : Type*} {b : ι → U}
    (hb : LinearIndependent K b) : LinearIndependent K (fun i => τ (b i)) := by
  rw [linearIndependent_iff'] at hb ⊢
  intro s c hc i hi
  have hτinv : ∀ (a : K) (u : U), τ (σ.symm a • u) = a • τ u := fun a u => by
    rw [hτ, RingEquiv.apply_symm_apply]
  have h0 : τ (∑ j ∈ s, σ.symm (c j) • b j) = 0 := by
    rw [map_sum]
    simp only [hτinv]
    exact hc
  have h1 : ∑ j ∈ s, σ.symm (c j) • b j = 0 := τ.injective (h0.trans (map_zero τ).symm)
  have h2 := hb s (fun j => σ.symm (c j)) h1 i hi
  rw [← RingEquiv.apply_symm_apply σ (c i), h2, map_zero]

theorem top_le_span_semilinear (σ : K ≃+* K) (τ : U ≃+ U)
    (hτ : ∀ (a : K) (u : U), τ (a • u) = σ a • τ u) {ι : Type*} [Fintype ι] (b : Basis ι K U) :
    ⊤ ≤ Submodule.span K (Set.range fun i => τ (b i)) := by
  intro u _
  have hu : u = ∑ i, σ (b.repr (τ.symm u) i) • τ (b i) := by
    conv_lhs => rw [← τ.apply_symm_apply u, ← b.sum_repr (τ.symm u)]
    rw [map_sum]
    simp only [hτ]
  rw [hu]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable [Module.Finite K U]

theorem trace_eq_of_semilinear_comm (σ : K ≃+* K) (τ : U ≃+ U)
    (hτ : ∀ (a : K) (u : U), τ (a • u) = σ a • τ u) (y z : U →ₗ[K] U)
    (hz : ∀ u, z (τ u) = τ (y u)) : LinearMap.trace K U z = σ (LinearMap.trace K U y) := by
  classical
  set b := Module.finBasis K U with hbdef
  set b' : Basis (Fin (finrank K U)) K U :=
    Basis.mk (linearIndependent_semilinear σ τ hτ b.linearIndependent)
      (top_le_span_semilinear σ τ hτ b) with hb'def
  have hb' : ∀ i, b' i = τ (b i) := fun i => Basis.mk_apply _ _ i
  rw [LinearMap.trace_eq_matrix_trace K b' z, LinearMap.trace_eq_matrix_trace K b y,
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    hb', hz]
  have hexp : τ (y (b i)) = ∑ j, σ (b.repr (y (b i)) j) • b' j := by
    conv_lhs => rw [← b.sum_repr (y (b i))]
    rw [map_sum]
    simp only [hτ, hb']
  rw [hexp, b'.repr_sum_self]

theorem trace_restrict_eq_of_semilinear {V : Type*} [AddCommGroup V] [Module K V]
    (σ : K ≃+* K) (T : V ≃+ V) (hT : ∀ (a : K) (v : V), T (a • v) = σ a • T v)
    (W : Submodule K V) [Module.Finite K W] (hTW : ∀ w ∈ W, T w ∈ W)
    (hTW' : ∀ w ∈ W, T.symm w ∈ W) (y z : V →ₗ[K] V) (hy : ∀ w ∈ W, y w ∈ W)
    (hzW : ∀ w ∈ W, z w ∈ W) (hz : ∀ v, z (T v) = T (y v)) :
    LinearMap.trace K W (z.restrict hzW) = σ (LinearMap.trace K W (y.restrict hy)) := by
  set τ : W ≃+ W :=
    { toFun := fun w => ⟨T (w : V), hTW w w.2⟩
      invFun := fun w => ⟨T.symm (w : V), hTW' w w.2⟩
      left_inv := fun w => Subtype.ext (T.symm_apply_apply (w : V))
      right_inv := fun w => Subtype.ext (T.apply_symm_apply (w : V))
      map_add' := fun v w => Subtype.ext (map_add T (v : V) (w : V)) } with hτdef
  refine trace_eq_of_semilinear_comm σ τ (fun a w => Subtype.ext (hT a (w : V))) _ _
    fun w => ?_
  apply Subtype.ext
  change z (T (w : V)) = T (y (w : V))
  exact hz w

end Semilinear

section Characteristic

theorem mem_inf_of_isPGroup {X : Type*} [Group X] (N₁ N₂ N₃ : Subgroup X)
    (hN : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup X)),
      ∀ M : Subgroup X, M.Normal → IsPGroup 2 M → M ≤ N)
    (hR : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃)) (hRn : (N₁ ⊓ N₂ ⊓ N₃).Normal) (θ : MulAut X) :
    ∀ r ∈ N₁ ⊓ N₂ ⊓ N₃, θ r ∈ N₁ ⊓ N₂ ⊓ N₃ := by
  set M := (N₁ ⊓ N₂ ⊓ N₃).map θ.toMonoidHom with hM
  have hMn : M.Normal := hRn.map _ θ.surjective
  have hMp : IsPGroup 2 M := hR.map θ.toMonoidHom
  intro r hr
  have hθr : θ r ∈ M := ⟨r, hr, rfl⟩
  exact ⟨⟨hN N₁ (by simp) M hMn hMp hθr, hN N₂ (by simp) M hMn hMp hθr⟩,
    hN N₃ (by simp) M hMn hMp hθr⟩

end Characteristic

section Lift

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem projLift_matrixProjectiveProjection (hQ : ∃ v, Q v ≠ 0) (B : matrixDerived Q) :
    projLift hQ (matrixProjectiveProjection Q B) = matrixLinearIso B.1 := by
  have h : matrixProjectiveProjection Q B = projHom Q (derivedEquiv Q B) := by
    simp only [projHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rw [h, projLift_projHom, coe_derivedEquiv]

theorem projLift_kappa_apply (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q)
    (x : matrixProjectiveDerived Q) (v : Fin d → K) :
    projLift hQ (matrixProjectiveConjugationHom Q g x) (coordinateSemilinearMap g.val v) =
      coordinateSemilinearMap g.val (projLift hQ x v) := by
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change projLift hQ (matrixProjectiveConjugation Q g (matrixProjectiveProjection Q B)) _ = _
  rw [matrixProjectiveConjugation_mk, projLift_matrixProjectiveProjection,
    projLift_matrixProjectiveProjection]
  have h := matrixConjugation_vector g.val B.val (coordinateSemilinearMap g.val v)
  rw [AddEquiv.symm_apply_apply] at h
  exact h

theorem trace_restrict_projLift_kappa (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q)
    (W : Submodule K (Fin d → K)) (hTW : ∀ w ∈ W, coordinateSemilinearMap g.val w ∈ W)
    (hTW' : ∀ w ∈ W, (coordinateSemilinearMap g.val).symm w ∈ W)
    (x : matrixProjectiveDerived Q) (hx : ∀ w ∈ W, projLift hQ x w ∈ W)
    (hx' : ∀ w ∈ W, projLift hQ (matrixProjectiveConjugationHom Q g x) w ∈ W) :
    LinearMap.trace K W
        (((projLift hQ (matrixProjectiveConjugationHom Q g x) :
          (Fin d → K) →ₗ[K] (Fin d → K))).restrict hx') =
      g.val.right (LinearMap.trace K W
        (((projLift hQ x : (Fin d → K) →ₗ[K] (Fin d → K))).restrict hx)) :=
  trace_restrict_eq_of_semilinear g.val.right (coordinateSemilinearMap g.val)
    (coordinateSemilinearMap_smul g.val) W hTW hTW' _ _ hx hx' (projLift_kappa_apply hQ g x)

theorem mapsTo_fixedSpace_kappa (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q)
    (R : Set (matrixProjectiveDerived Q))
    (hR : ∀ r ∈ R, (matrixProjectiveConjugationHom Q g)⁻¹ r ∈ R) {v : Fin d → K}
    (hv : ∀ r ∈ R, projLift hQ r v = v) :
    ∀ r ∈ R, projLift hQ r (coordinateSemilinearMap g.val v) = coordinateSemilinearMap g.val v := by
  intro r hr
  have hr' : matrixProjectiveConjugationHom Q g ((matrixProjectiveConjugationHom Q g)⁻¹ r) = r :=
    MulAut.apply_inv_self _ _ _
  rw [← hr', projLift_kappa_apply, hv _ (hR r hr)]

theorem mapsTo_fixedSpace_of_core [Finite K] (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q)
    {X : Subgroup (matrixProjectiveDerived Q)}
    (hgX : ∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) (N₁ N₂ N₃ : Subgroup ↥X)
    (hN : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → IsPGroup 2 M → M ≤ N)
    (hR : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃)) (hRn : (N₁ ⊓ N₂ ⊓ N₃).Normal) {v : Fin d → K}
    (hv : ∀ r ∈ N₁ ⊓ N₂ ⊓ N₃, projLift hQ (r : matrixProjectiveDerived Q) v = v) :
    ∀ r ∈ N₁ ⊓ N₂ ⊓ N₃, projLift hQ (r : matrixProjectiveDerived Q)
      (coordinateSemilinearMap g.val v) = coordinateSemilinearMap g.val v := by
  set β := matrixProjectiveConjugationHom Q g with hβ
  have hgX' : ∀ x ∈ X, β⁻¹ x ∈ X := by
    intro x hx
    have heq := subgroup_map_eq_of_mapsTo β hgX
    rw [← heq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change β⁻¹ (β y) ∈ X
    rwa [MulAut.inv_apply_self]
  set θ := restrictAutOfMapsTo β⁻¹ X hgX' with hθ
  intro r hr
  have hr' := mem_inf_of_isPGroup N₁ N₂ N₃ hN hR hRn θ r hr
  have hβr : β ((θ r : ↥X) : matrixProjectiveDerived Q) = (r : matrixProjectiveDerived Q) := by
    rw [hθ, coe_restrictAutOfMapsTo]
    exact MulAut.apply_inv_self _ _ _
  rw [← hβr, hβ, projLift_kappa_apply, hv _ hr']

end Lift

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] [CharP K 2] in
theorem exists_coordinateQuadPlus_ne_zero (hn : 1 ≤ n) :
    ∃ v, coordinateQuadPlus n K v ≠ 0 := by
  classical
  set i : Fin n := ⟨0, hn⟩
  set e := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.plusIndexEquiv n
  refine ⟨Pi.single (e (.inl i)) 1 + Pi.single (e (.inr i)) 1, ?_⟩
  rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus_apply]
  have hne : ∀ a b : Fin n ⊕ Fin n, a ≠ b → e a ≠ e b := fun a b h h' => h (e.injective h')
  rw [Finset.sum_eq_single i]
  · simp only [Pi.add_apply]
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (hne _ _ Sum.inl_ne_inr), Pi.single_eq_same,
      Pi.single_eq_of_ne (hne _ _ Sum.inr_ne_inl), add_zero, zero_add, one_mul]
    exact one_ne_zero
  · intro j _ hj
    have h1 : e (.inl j) ≠ e (.inl i) := hne _ _ (fun h => hj (Sum.inl_injective h))
    have h2 : e (.inl j) ≠ e (.inr i) := hne _ _ Sum.inl_ne_inr
    simp only [Pi.add_apply]
    rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, add_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [CharP K 2] in
theorem exists_kappa_eq_plus (hn : 5 ≤ n)
    (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    ∃ g : similarityPairs (coordinateQuadPlus n K),
      matrixProjectiveConjugationHom (coordinateQuadPlus n K) g = β := by
  have h : β ∈ matrixProjectiveImage (coordinateQuadPlus n K) := by
    rw [plusImage_eq_top hn]
    exact mem_top β
  exact h

theorem trace_projLift_map_plus (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
    LinearMap.trace K _ (projLift (exists_coordinateQuadPlus_ne_zero (by omega)) (β x) :
        (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) =
      plusFieldPart hf hK hn β (LinearMap.trace K _
        (projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x :
          (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K))) := by
  obtain ⟨g, rfl⟩ := exists_kappa_eq_plus hn β
  rw [plusFieldPart, orthAutFieldPart_kappa]
  exact trace_eq_of_semilinear_comm g.val.right (coordinateSemilinearMap g.val)
    (coordinateSemilinearMap_smul g.val) _ _
    (projLift_kappa_apply (exists_coordinateQuadPlus_ne_zero (by omega)) g x)

theorem spLeviSection_of_trace_eq_plus (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {X : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))} {r : ℕ} (hr : 1 ≤ r)
    (ρ : ↥X →* CFSG.Assembly.LowTwoRank.StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) =
      LinearMap.trace K _ (projLift (exists_coordinateQuadPlus_ne_zero (by omega))
        (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
          (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K))) :
    SpLeviSection (plusFieldPart hf hK hn) X ρ.ker :=
  spLeviSection_of_hom _ hr ρ hρ fun β hβ _ x => by
    rw [htr, htr, coe_restrictAutOfMapsTo]
    exact trace_projLift_map_plus hf hK hn β x

end Plus

end CFSG.SeitzReduction.OmegaPilot
