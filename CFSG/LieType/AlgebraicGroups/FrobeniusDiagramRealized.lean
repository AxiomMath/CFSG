module

public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramComorphism
public import CFSG.LieType.AlgebraicGroups.ExactAffineRealization
public import CFSG.LieType.AlgebraicGroups.TwistedOrbitSurjectivity
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.LieType.Chevalley.ExactNormalFormE
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

open scoped CFSG.ConvolutionPoints

section Realized

variable (τ : Tag) (L : Type) [Field L] [IsAlgClosed L]

abbrev realizedCoord : Type :=
  GLCoord L (Label τ) ⧸ subgroupIdeal (adjointPointSubgroup τ L)

theorem isConnectedAlgebraicSubgroup_adjointPointSubgroup :
    IsConnectedAlgebraicSubgroup L (adjointPointSubgroup τ L) :=
  (exceptional_Lang_exact_affine_group_realization L τ).1.2.1

instance smooth_realizedCoord :
    Algebra.Smooth L (realizedCoord τ L) :=
  (exceptional_Lang_exact_affine_group_realization L τ).1.2.2.1

instance isDomain_realizedCoord :
    IsDomain (realizedCoord τ L) :=
  (isConnectedAlgebraicSubgroup_adjointPointSubgroup τ L).isDomain

instance connectedSpace_realizedCoord :
    ConnectedSpace (PrimeSpectrum (realizedCoord τ L)) :=
  (isConnectedAlgebraicSubgroup_adjointPointSubgroup τ L).connectedSpace

@[expose] def realizedPointEquiv :
    WithConv (realizedCoord τ L →ₐ[L] L) ≃* adjointGroup τ L :=
  (subgroupQuotientPointsEquiv _
    (isConnectedAlgebraicSubgroup_adjointPointSubgroup τ L).pointsZero_eq).trans
    ((modGLPoint τ L).subgroupMap (adjointGroup τ L)).symm

theorem coe_realizedPointEquiv
    (φ : WithConv (realizedCoord τ L →ₐ[L] L)) :
    (realizedPointEquiv τ L φ : ModGL τ L) =
      (modGLPoint τ L).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ L _))) :=
  rfl

omit [IsAlgClosed L] in
theorem mem_subgroupPoints_adjointPointSubgroup
    {y : GLCoord L (Label τ) →ₐ[L] L} :
    y ∈ subgroupPoints (adjointPointSubgroup τ L) ↔
      (modGLPoint τ L).symm (toConv y) ∈ adjointGroup τ L := by
  rw [subgroupPoints_map, transportPoints_modGLPoint]
  rfl

end Realized

section FrobeniusTwist

variable {τ : Tag} {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

variable (τ L) in
abbrev entrywiseFrobGL (e : ℕ) : ModGL τ L →* ModGL τ L :=
  Units.map (entrywiseHom (iterateFrobenius L p e))

variable (τ L) in
abbrev frobTwistGL (e : ℕ) (Q : ModGL τ L) : ModGL τ L →* ModGL τ L :=
  (MulAut.conj Q).toMonoidHom.comp (entrywiseFrobGL τ L p e)

theorem frobTwistGL_apply (e : ℕ) (Q g : ModGL τ L) :
    frobTwistGL τ L p e Q g = Q * entrywiseFrobGL τ L p e g * Q⁻¹ :=
  rfl

theorem entrywiseFrobGL_mem
    [IsAlgClosed L] (e : ℕ) {g : ModGL τ L} (hg : g ∈ adjointGroup τ L) :
    entrywiseFrobGL τ L p e g ∈ adjointGroup τ L := by
  have h := map_exactEntrywiseAut (τ := τ) (iterateFrobeniusEquiv L p e) (Or.inl rfl)
  rw [← h]
  exact ⟨g, hg, rfl⟩

@[expose] def frobTwistCoGL (e : ℕ) (Q : ModGL τ L) :
    GLCoord L (Label τ) →ₐ[L] GLCoord L (Label τ) :=
  (frobCo p e).comp (innerCo (modGLPoint τ L Q))

theorem toConv_comp_frobCo (e : ℕ) (y : GLCoord L (Label τ) →ₐ[L] L) :
    toConv (y.comp (frobCo p e)) =
      modGLPoint τ L (entrywiseFrobGL τ L p e ((modGLPoint τ L).symm (toConv y))) := by
  apply WithConv.ext
  refine GLCoord.algHom_ext_of_entries fun a b => ?_
  rw [ofConv_toConv, AlgHom.comp_apply, frobCo_glEntry, map_pow, modGLPoint_apply_glEntry,
    Units.coe_map]
  change _ = (entrywise (iterateFrobenius L p e)
    (((modGLPoint τ L).symm (toConv y) : ModGL τ L) : Module.End L (RootModule τ L)))
      (Finsupp.single b 1) a
  rw [entrywise_single, Finsupp.mapRange_apply, ← modGLPoint_apply_glEntry,
    MulEquiv.apply_symm_apply, ofConv_toConv, iterateFrobenius_def]

theorem modGLPoint_symm_comp_frobTwistCoGL (e : ℕ) (Q : ModGL τ L)
    (y : GLCoord L (Label τ) →ₐ[L] L) :
    (modGLPoint τ L).symm (toConv (y.comp (frobTwistCoGL p e Q))) =
      frobTwistGL τ L p e Q ((modGLPoint τ L).symm (toConv y)) := by
  have h := point_comp_innerCo (toConv (y.comp (frobCo p e))) (modGLPoint τ L Q)
  rw [ofConv_toConv, toConv_comp_frobCo, ← map_inv, ← map_mul, ← map_mul] at h
  rw [frobTwistCoGL, ← AlgHom.comp_assoc, h, MulEquiv.symm_apply_apply]
  rfl

theorem frobTwistCoGL_pointMul (e : ℕ) (Q : ModGL τ L)
    (y z : WithConv (GLCoord L (Label τ) →ₐ[L] L)) :
    toConv ((y * z).ofConv.comp (frobTwistCoGL p e Q)) =
      toConv (y.ofConv.comp (frobTwistCoGL p e Q)) *
        toConv (z.ofConv.comp (frobTwistCoGL p e Q)) := by
  apply (modGLPoint τ L).symm.injective
  rw [map_mul, modGLPoint_symm_comp_frobTwistCoGL, modGLPoint_symm_comp_frobTwistCoGL,
    modGLPoint_symm_comp_frobTwistCoGL, toConv_ofConv, toConv_ofConv, toConv_ofConv, map_mul,
    map_mul]

theorem frobTwistCoGL_mem
    [IsAlgClosed L] (e : ℕ) {Q : ModGL τ L}
    (hQ : ∀ g ∈ adjointGroup τ L, Q * g * Q⁻¹ ∈ adjointGroup τ L) :
    ∀ y ∈ subgroupPoints (adjointPointSubgroup τ L),
      y.comp (frobTwistCoGL p e Q) ∈ subgroupPoints (adjointPointSubgroup τ L) := by
  intro y hy
  rw [mem_subgroupPoints_adjointPointSubgroup] at hy ⊢
  rw [modGLPoint_symm_comp_frobTwistCoGL, frobTwistGL_apply]
  exact hQ _ (entrywiseFrobGL_mem p e hy)

variable [IsAlgClosed L]

@[expose] def frobTwistCo
    (e : ℕ) (Q : ModGL τ L)
    (hQ : ∀ g ∈ adjointGroup τ L, Q * g * Q⁻¹ ∈ adjointGroup τ L) :
    realizedCoord τ L →ₐc[L] realizedCoord τ L :=
  bialgHomOfPointMul
    (quotientCo (adjointPointSubgroup τ L) (frobTwistCoGL p e Q) (frobTwistCoGL_mem p e hQ))
    (quotientCo_pointMul _ _ _ (frobTwistCoGL_pointMul p e Q))

theorem coe_frobTwistCo
    (e : ℕ) (Q : ModGL τ L)
    (hQ : ∀ g ∈ adjointGroup τ L, Q * g * Q⁻¹ ∈ adjointGroup τ L) :
    (frobTwistCo p e Q hQ : realizedCoord τ L →ₐ[L] realizedCoord τ L) =
      quotientCo (adjointPointSubgroup τ L) (frobTwistCoGL p e Q) (frobTwistCoGL_mem p e hQ) :=
  rfl

theorem realizedPointEquiv_comp_frobTwistCo
    (e : ℕ) (Q : ModGL τ L)
    (hQ : ∀ g ∈ adjointGroup τ L, Q * g * Q⁻¹ ∈ adjointGroup τ L)
    (φ : realizedCoord τ L →ₐ[L] L) :
    (realizedPointEquiv τ L (toConv (φ.comp (frobTwistCo p e Q hQ : realizedCoord τ L →ₐ[L] _))) :
        ModGL τ L) =
      frobTwistGL τ L p e Q (realizedPointEquiv τ L (toConv φ)) := by
  rw [coe_realizedPointEquiv, coe_realizedPointEquiv, ofConv_toConv, ofConv_toConv,
    coe_frobTwistCo, comp_quotientCo_comp_mkₐ, modGLPoint_symm_comp_frobTwistCoGL]

theorem realizedPointEquiv_pointMap
    (e : ℕ) (Q : ModGL τ L)
    (hQ : ∀ g ∈ adjointGroup τ L, Q * g * Q⁻¹ ∈ adjointGroup τ L)
    (φ : WithConv (realizedCoord τ L →ₐ[L] L)) :
    (realizedPointEquiv τ L (pointMap (frobTwistCo p e Q hQ) φ) : ModGL τ L) =
      frobTwistGL τ L p e Q (realizedPointEquiv τ L φ) :=
  realizedPointEquiv_comp_frobTwistCo p e Q hQ φ.ofConv

theorem tangent_comp_frobTwistCo
    {e : ℕ} (he : 1 ≤ e) (Q : ModGL τ L)
    (hQ : ∀ g ∈ adjointGroup τ L, Q * g * Q⁻¹ ∈ adjointGroup τ L)
    {D : realizedCoord τ L →ₗ[L] L}
    (hD : D ∈ tangentSpace L (realizedCoord τ L) (Bialgebra.counitAlgHom L _)) :
    D ∘ₗ (frobTwistCo p e Q hQ : realizedCoord τ L →ₐ[L] realizedCoord τ L).toLinearMap = 0 := by
  set π := Ideal.Quotient.mkₐ L (subgroupIdeal (adjointPointSubgroup τ L))
  have hDπ : D ∘ₗ π.toLinearMap ∈
      tangentSpace L (GLCoord L (Label τ)) ((Bialgebra.counitAlgHom L _).comp π) :=
    (tangentMap π rfl ⟨D, hD⟩).2
  have h0 := tangent_comp_frobCo p he hDπ
  refine LinearMap.ext fun b => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective L _ b
  have h1 := congrArg (fun f : GLCoord L (Label τ) →ₗ[L] L =>
    f (innerCo (modGLPoint τ L Q) a)) h0
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply] at h1
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply, coe_frobTwistCo]
  change D (quotientCo _ _ _ (π a)) = 0
  rw [← AlgHom.comp_apply (quotientCo _ _ _) π, quotientCo_comp_mkₐ, AlgHom.comp_apply,
    frobTwistCoGL, AlgHom.comp_apply]
  exact h1

@[expose] def frobTwistAut
    (e : ℕ) (Q : ModGL τ L)
    (hQ : (adjointGroup τ L).map (MulAut.conj Q).toMonoidHom = adjointGroup τ L) :
    MulAut (adjointGroup τ L) :=
  mulAutRestrict (adjointGroup τ L) (MulAut.conj Q) hQ *
    entrywiseAdjointAut τ (iterateFrobeniusEquiv L p e)

theorem coe_frobTwistAut
    (e : ℕ) (Q : ModGL τ L)
    (hQ : (adjointGroup τ L).map (MulAut.conj Q).toMonoidHom = adjointGroup τ L)
    (g : adjointGroup τ L) :
    (frobTwistAut p e Q hQ g : ModGL τ L) = frobTwistGL τ L p e Q g :=
  rfl

omit [IsAlgClosed L] in
theorem conj_mem_adjointGroup_of_map_eq {Q : ModGL τ L}
    (hQ : (adjointGroup τ L).map (MulAut.conj Q).toMonoidHom = adjointGroup τ L) :
    ∀ g ∈ adjointGroup τ L, Q * g * Q⁻¹ ∈ adjointGroup τ L := fun g hg => by
  rw [← hQ]
  exact ⟨g, hg, rfl⟩

theorem exists_eq_inv_mul_frobTwistAut
    {e : ℕ} (he : 1 ≤ e) (Q : ModGL τ L)
    (hQ : (adjointGroup τ L).map (MulAut.conj Q).toMonoidHom = adjointGroup τ L)
    (x : adjointGroup τ L) : ∃ h : adjointGroup τ L, x = h⁻¹ * frobTwistAut p e Q hQ h := by
  obtain ⟨h, hh⟩ := exceptional_Lang_connected_twisted_orbit_surjectivity
    (frobTwistCo p e Q (conj_mem_adjointGroup_of_map_eq hQ)) (le_refl 1)
    (fun D hD => by
      rw [pow_one]
      exact tangent_comp_frobTwistCo p he Q _ hD) ((realizedPointEquiv τ L).symm x)
  refine ⟨realizedPointEquiv τ L h, ?_⟩
  have hx := congrArg (realizedPointEquiv τ L) hh
  rw [MulEquiv.apply_symm_apply, map_mul, map_inv] at hx
  rw [hx]
  congr 1
  apply Subtype.ext
  rw [realizedPointEquiv_pointMap, coe_frobTwistAut]

end FrobeniusTwist

section Iterate

variable {τ : Tag} {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

theorem iterateFrobenius_comp_iterateFrobenius (m n : ℕ) :
    (iterateFrobenius L p m).comp (iterateFrobenius L p n) = iterateFrobenius L p (n + m) := by
  ext x
  simp only [RingHom.comp_apply, iterateFrobenius_def, ← pow_mul, ← pow_add]

theorem entrywiseFrobGL_frobGL (m n : ℕ) (g : ModGL τ L) :
    entrywiseFrobGL τ L p m (entrywiseFrobGL τ L p n g) = entrywiseFrobGL τ L p (n + m) g := by
  ext1
  change entrywise _ (entrywise _ _) = entrywise _ _
  rw [entrywise_entrywise, iterateFrobenius_comp_iterateFrobenius]

theorem entrywiseFrobGL_zero (g : ModGL τ L) : entrywiseFrobGL τ L p 0 g = g := by
  ext1
  change entrywise (iterateFrobenius L p 0) _ = _
  have h : iterateFrobenius L p 0 = RingHom.id L := by
    ext x
    simp
  rw [h, entrywise_id]

theorem frobTwistGL_iterate (e : ℕ) {Q : ModGL τ L} (hQ : entrywiseFrobGL τ L p e Q = Q) (n : ℕ)
    (g : ModGL τ L) :
    (frobTwistGL τ L p e Q)^[n] g = Q ^ n * entrywiseFrobGL τ L p (e * n) g * (Q ^ n)⁻¹ := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, mul_zero, entrywiseFrobGL_zero, one_mul,
      inv_one, mul_one]
  | succ n ih =>
    have hQn : entrywiseFrobGL τ L p e (Q ^ n) = Q ^ n := by rw [map_pow, hQ]
    rw [Function.iterate_succ_apply', ih, frobTwistGL_apply, map_mul, map_mul, map_inv, hQn,
      entrywiseFrobGL_frobGL, pow_succ', mul_add, mul_one, mul_inv_rev]
    group

theorem comp_pow_eq_iterate {B : Type} [CommRing B] [Algebra L B] (f : B →ₐ[L] B)
    (x : B →ₐ[L] L) (n : ℕ) : x.comp (f ^ n) = (fun y => y.comp f)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ_apply', ← ih]
    rfl

variable [IsAlgClosed L]

theorem realizedPointEquiv_comp_frobTwistCo_iterate
    (e : ℕ) (Q : ModGL τ L)
    (hQ : ∀ g ∈ adjointGroup τ L, Q * g * Q⁻¹ ∈ adjointGroup τ L) (n : ℕ)
    (φ : realizedCoord τ L →ₐ[L] L) :
    (realizedPointEquiv τ L (toConv ((fun y : realizedCoord τ L →ₐ[L] L =>
        y.comp (frobTwistCo p e Q hQ : realizedCoord τ L →ₐ[L] realizedCoord τ L))^[n] φ)) :
        ModGL τ L) =
      (frobTwistGL τ L p e Q)^[n] (realizedPointEquiv τ L (toConv φ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      realizedPointEquiv_comp_frobTwistCo, ih]

theorem frobTwistCo_pow
    (e : ℕ) {Q : ModGL τ L}
    (hQ : ∀ g ∈ adjointGroup τ L, Q * g * Q⁻¹ ∈ adjointGroup τ L)
    (hQF : entrywiseFrobGL τ L p e Q = Q) {n : ℕ} (hn : Q ^ n = 1) :
    (frobTwistCo p e Q hQ : realizedCoord τ L →ₐ[L] realizedCoord τ L) ^ n =
      (frobTwistCo (τ := τ) (L := L) p (e * n) 1 (fun g hg => by rwa [one_mul, inv_one, mul_one]) :
        realizedCoord τ L →ₐ[L] realizedCoord τ L) := by
  refine (exceptional_Lang_affine_point_and_product_geometry L).2.2.2.2.1 _ _ _ _ fun x => ?_
  apply toConv_injective
  apply (realizedPointEquiv τ L).injective
  apply Subtype.ext
  rw [comp_pow_eq_iterate, realizedPointEquiv_comp_frobTwistCo_iterate,
    realizedPointEquiv_comp_frobTwistCo, frobTwistGL_iterate p e hQF, hn, one_mul, inv_one,
    mul_one, frobTwistGL_apply, one_mul, inv_one, mul_one]

end Iterate

section Diagram

variable (t : TwistTag) (L : Type) [Field L]

theorem coe_diagramConjAut_zpow
    (j : ℤ) (g : adjointGroup t.tag L) :
    ((diagramConjAut t L ^ j) g : ModGL t.tag L) =
      diagramMap t L ^ j * g * (diagramMap t L ^ j)⁻¹ := by
  induction j using Int.induction_on generalizing g with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, MulAut.mul_apply, ih, coe_diagramConjAut, zpow_add_one]
    group
  | pred i ih =>
    have hinv : (((diagramConjAut t L)⁻¹ g : adjointGroup t.tag L) : ModGL t.tag L) =
        (diagramMap t L)⁻¹ * g * diagramMap t L := by
      have h := coe_diagramConjAut t L ((diagramConjAut t L)⁻¹ g)
      rw [MulAut.apply_inv_self] at h
      rw [h]
      group
    rw [zpow_sub_one, MulAut.mul_apply, ih, hinv, zpow_sub_one]
    group

theorem map_conj_diagramMap_zpow
    (j : ℤ) :
    (adjointGroup t.tag L).map (MulAut.conj (diagramMap t L ^ j)).toMonoidHom =
      adjointGroup t.tag L := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    have := ((diagramConjAut t L ^ j) ⟨h, hh⟩).2
    rwa [coe_diagramConjAut_zpow] at this
  · intro hg
    refine ⟨((diagramConjAut t L ^ (-j)) ⟨g, hg⟩ : ModGL t.tag L),
      ((diagramConjAut t L ^ (-j)) ⟨g, hg⟩).2, ?_⟩
    change diagramMap t L ^ j * _ * (diagramMap t L ^ j)⁻¹ = g
    rw [coe_diagramConjAut_zpow, zpow_neg]
    group

variable {L} (p : ℕ) [Fact p.Prime] [CharP L p]

theorem entrywiseFrobGL_diagramMap_zpow (e : ℕ) (j : ℤ) :
    entrywiseFrobGL t.tag L p e (diagramMap t L ^ j) = diagramMap t L ^ j := by
  rw [map_zpow, units_map_entrywiseHom_diagramMap]

theorem diagramMap_zpow_pow_order
    (j : ℤ) : (diagramMap t L ^ j) ^ t.order = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, diagramMap_pow_order,
    one_zpow]

end Diagram

end CFSG.LieType.AlgebraicGroups

namespace CFSG.StandardType.F4ExplicitPos.LangPosition

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

public section

private theorem mapRange_smul_ringHom_no117 {τ : Tag} {K : Type} [Field K] (σ : K →+* K) (c : K)
    (x : RootModule τ K) :
    Finsupp.mapRange σ σ.map_zero (c • x) = σ c • Finsupp.mapRange σ σ.map_zero x := by
  ext a
  simp

theorem entrywise_sum_smul_no117 {τ : Tag} {K : Type} [Field K] (σ : K →+* K) {ι : Type}
    (s : Finset ι) (c : ι → K) (A : ι → Module.End K (RootModule τ K)) :
    entrywise σ (∑ k ∈ s, c k • A k) = ∑ k ∈ s, σ (c k) • entrywise σ (A k) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, entrywise_single]
  rw [Finsupp.mapRange_finsetSum σ]
  simp only [mapRange_smul_ringHom_no117]

theorem entrywise_xCoeff_no117 {τ : Tag} {K : Type} [Field K]
    (σ : K →+* K)
    (i : Fin τ.rank) (k : ℕ) :
    entrywise σ (xCoeff τ K i k) = xCoeff τ K i k := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, mapRange_xCoeff_single]

theorem entrywise_yCoeff_no117 {τ : Tag} {K : Type} [Field K]
    (σ : K →+* K)
    (i : Fin τ.rank) (k : ℕ) :
    entrywise σ (yCoeff τ K i k) = yCoeff τ K i k := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, mapRange_yCoeff_single]

theorem entrywise_xOp_no117 {τ : Tag} {K : Type} [Field K]
    (σ : K →+* K)
    (i : Fin τ.rank) (c : K) :
    entrywise σ (xOp τ K i c) = xOp τ K i (σ c) := by
  simp only [xOp_eq_sum_xCoeff, entrywise_sum_smul_no117, entrywise_xCoeff_no117, map_pow]

theorem entrywise_yOp_no117 {τ : Tag} {K : Type} [Field K]
    (σ : K →+* K)
    (i : Fin τ.rank) (c : K) :
    entrywise σ (yOp τ K i c) = yOp τ K i (σ c) := by
  simp only [yOp_eq_sum_yCoeff, entrywise_sum_smul_no117, entrywise_yCoeff_no117, map_pow]

theorem entrywiseFrobGL_letterUnit_no117 {τ : Tag} {k : Type} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p]
    (e : ℕ) (l : Letter τ) (c : k) :
    entrywiseFrobGL τ k p e (letterUnit τ k l c) = letterUnit τ k l (c ^ p ^ e) := by
  unfold letterUnit
  split_ifs
  · refine Units.ext ?_
    rw [Units.coe_map, coe_xUnit, coe_xUnit]
    exact (entrywise_xOp_no117 (iterateFrobenius k p e) l.1 c).trans
      (by rw [iterateFrobenius_def])
  · refine Units.ext ?_
    rw [Units.coe_map, coe_yUnit, coe_yUnit]
    exact (entrywise_yOp_no117 (iterateFrobenius k p e) l.1 c).trans
      (by rw [iterateFrobenius_def])

theorem entrywiseFrobGL_xUnit_no117 {τ : Tag} {k : Type} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p]
    (e : ℕ) (i : Fin τ.rank) (c : k) :
    entrywiseFrobGL τ k p e (xUnit τ k i c) = xUnit τ k i (c ^ p ^ e) :=
  entrywiseFrobGL_letterUnit_no117 p e (i, true) c

theorem entrywiseFrobGL_yUnit_no117 {τ : Tag} {k : Type} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p]
    (e : ℕ) (i : Fin τ.rank) (c : k) :
    entrywiseFrobGL τ k p e (yUnit τ k i c) = yUnit τ k i (c ^ p ^ e) :=
  entrywiseFrobGL_letterUnit_no117 p e (i, false) c

theorem entrywiseFrobGL_wordUnit_no117 {τ : Tag} {k : Type} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p]
    (e : ℕ) (w : List (Letter τ × k)) :
    entrywiseFrobGL τ k p e (wordUnit τ k w) =
      wordUnit τ k (mapWord (iterateFrobenius k p e) w) := by
  induction w with
  | nil => rw [wordUnit_nil, mapWord, List.map_nil, wordUnit_nil, map_one]
  | cons a w ih =>
    rw [wordUnit_cons, mapWord_cons, wordUnit_cons, map_mul, ih,
      entrywiseFrobGL_letterUnit_no117, iterateFrobenius_def]

theorem entrywiseFrobGL_pinnedX_no117 {τ : Tag} {k : Type} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p]
    (e : ℕ) (α : Fin τ.rank → ℤ) (c : k) :
    entrywiseFrobGL τ k p e (pinnedX τ k α c) =
      pinnedX τ k α (iterateFrobenius k p e c) := by
  rw [← wordUnit_pinnedWord (τ := τ) (R := k) α c, entrywiseFrobGL_wordUnit_no117,
    mapWord_pinnedWord, wordUnit_pinnedWord]

theorem entrywiseFrobGL_mem_adjointGroup_no117 {τ : Tag} {k : Type} [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p]
    (e : ℕ) {g : ModGL τ k} (hg : g ∈ adjointGroup τ k) :
    entrywiseFrobGL τ k p e g ∈ adjointGroup τ k := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, c, h | h⟩ := hy
    · rw [show y = xUnit τ k i c from Units.ext h, entrywiseFrobGL_xUnit_no117]
      exact xUnit_mem_adjointGroup _ _
    · rw [show y = yUnit τ k i c from Units.ext h, entrywiseFrobGL_yUnit_no117]
      exact yUnit_mem_adjointGroup _ _
  | one => simp
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx


end

end CFSG.StandardType.F4ExplicitPos.LangPosition
