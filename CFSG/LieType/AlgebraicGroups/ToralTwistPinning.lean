module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
public import CFSG.LieType.Chevalley.LatticeCharacterInterpolation
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped CFSG.ConvolutionPoints

section Character

variable {τ : Tag} {k : Type} [Field k]

@[expose] def signCharTuple (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) : Fin τ.rank → kˣ :=
  fun i => intUnitsMap k (χ (Multiplicative.ofAdd (Pi.single i 1)))

theorem rootChar_signCharTuple (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ)
    (v : Fin τ.rank → ℤ) :
    rootChar (signCharTuple (k := k) χ) v = intUnitsMap k (χ (Multiplicative.ofAdd v)) := by
  have hv : Multiplicative.ofAdd v =
      ∏ i, Multiplicative.ofAdd (v i • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    rw [← ofAdd_sum]
    congr 1
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hv, map_prod, map_prod, rootChar]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow, map_zpow, signCharTuple]

theorem signCharTuple_sign (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : Fin τ.rank) :
    signCharTuple (k := k) χ i = 1 ∨ signCharTuple (k := k) χ i = -1 := by
  rcases Int.units_eq_one_or (χ (Multiplicative.ofAdd (Pi.single i 1))) with h | h
  · left
    rw [signCharTuple, h, map_one]
  · right
    rw [signCharTuple, h]
    exact Units.ext (by simp [intUnitsMap])

theorem rootCharKernel_signCharTuple
    (hk : ringChar k ≠ 2)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    rootCharKernel (signCharTuple (k := k) χ) = kernelRoots χ := by
  ext α
  refine and_congr_right fun _ => ?_
  rw [rootChar_signCharTuple, map_eq_one_iff _ (intUnitsMap_injective hk)]

end Character

section Main

variable (p : ℕ) [Fact p.Prime] {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem map_frobTwistGL_rootSpan_kernelRoots
    (e : ℕ)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} {Q : ModGL τ k} (hQ : Q ∈ monomialSubgroup τ k)
    (hω : weylQuotientHom τ k ⟨Q, hQ⟩ ∈ charStabilizer χ) :
    (rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e Q) = rootSpan τ k (kernelRoots χ) := by
  rw [map_frobTwistGL_rootSpan p e hQ fun α hα => hα.1]
  congr 1
  apply le_antisymm
  · rintro _ ⟨α, hα, rfl⟩
    exact smul_mem_kernelRoots hω hα
  · intro α hα
    exact ⟨(weylQuotientHom τ k ⟨Q, hQ⟩)⁻¹ • α, smul_mem_kernelRoots (inv_mem hω) hα,
      smul_inv_smul _ α⟩

theorem map_frobTwistGL_torusGroup_sup_rootSpan
    (e : ℕ)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} {Q : ModGL τ k} (hQ : Q ∈ monomialSubgroup τ k)
    (hQT : Q ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hω : weylQuotientHom τ k ⟨Q, hQ⟩ ∈ charStabilizer χ) :
    (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e Q) =
      torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) := by
  rw [Subgroup.map_sup, map_frobTwistGL_torusGroup p e hQT,
    map_frobTwistGL_rootSpan_kernelRoots p e hQ hω]

omit [IsAlgClosed k] in
theorem rootDiagUnit_conj_rootSL2
    (c : Fin τ.rank → kˣ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (z : k) :
    rootDiagUnit τ c * rootSL2 τ k γ (uSL z) * (rootDiagUnit τ c)⁻¹ =
        rootSL2 τ k γ (uSL ((rootChar c γ : k) * z)) ∧
      rootDiagUnit τ c * rootSL2 τ k γ (vSL z) * (rootDiagUnit τ c)⁻¹ =
        rootSL2 τ k γ (vSL ((((rootChar c γ)⁻¹ : kˣ) : k) * z)) := by
  obtain ⟨η, -, hv⟩ := exists_rootSL2_vSL_eq (K := k) hγ
  have hneg : rootChar c (-γ) = (rootChar c γ)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← rootChar_add, neg_add_cancel, rootChar_zero]
  refine ⟨?_, ?_⟩
  · rw [rootSL2_uSL_eq, rootDiagUnit_conj_pinnedX c hγ, rootSL2_uSL_eq, mul_smul_comm]
  · rw [hv, rootDiagUnit_conj_pinnedX c (IsRoot.neg hγ), hv, hneg, mul_left_comm]

omit [IsAlgClosed k] in
theorem finite_setOf_entrywiseFrobGL_eq {n : ℕ} (hn : 1 ≤ n) :
    {g : ModGL τ k | entrywiseFrobGL τ k p n g = g}.Finite := by
  classical
  set P : Polynomial k := Polynomial.X ^ (p ^ n) - Polynomial.X with hPdef
  have hq : 1 < p ^ n := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq
  let φ : ModGL τ k → Label τ → Label τ → k := fun g b l =>
    ((g : Module.End k (RootModule τ k)) (Finsupp.single b 1)) l
  have hφ : Function.Injective φ := fun g g' h =>
    Units.ext (end_ext_single fun b => Finsupp.ext fun l => congrFun (congrFun h b) l)
  have hsub : {g : ModGL τ k | entrywiseFrobGL τ k p n g = g} ⊆
      φ ⁻¹' (Set.univ.pi fun _ => Set.univ.pi fun _ => P.rootSet k) := by
    intro g hg b _ l _
    have h1 := congrArg (fun A : ModGL τ k =>
      ((A : Module.End k (RootModule τ k)) (Finsupp.single b 1)) l) hg
    simp only [Units.coe_map] at h1
    change (entrywise (iterateFrobenius k p n) (g : Module.End k (RootModule τ k))
      (Finsupp.single b 1)) l = _ at h1
    rw [entrywise_single, Finsupp.mapRange_apply, iterateFrobenius_def] at h1
    rw [Polynomial.mem_rootSet]
    refine ⟨hP, ?_⟩
    simp only [hPdef, map_sub, map_pow, Polynomial.aeval_X]
    rw [h1, sub_self]
  exact ((Set.Finite.pi fun _ => Set.Finite.pi fun _ => Polynomial.rootSet_finite P k).preimage
    hφ.injOn).subset hsub

omit [IsAlgClosed k] in
theorem pow_smul_mem_of_forall
    {ω : WeylGroup τ} {Δ : Set (Fin τ.rank → ℤ)}
    (hΔ : ∀ β ∈ Δ, ω • β ∈ Δ) (m : ℕ) : ∀ β ∈ Δ, ω ^ m • β ∈ Δ := by
  induction m with
  | zero => intro β hβ; rwa [pow_zero, one_smul]
  | succ m ih => intro β hβ; rw [pow_succ', mul_smul]; exact hΔ _ (ih β hβ)

omit [IsAlgClosed k] in
theorem iterate_frobTwistGL_rootSL2
    (e : ℕ) {Q : ModGL τ k} {ω : WeylGroup τ}
    {Δ : Set (Fin τ.rank → ℤ)} (hΔ : ∀ β ∈ Δ, ω • β ∈ Δ)
    (hpin : ∀ β ∈ Δ, ∀ A : SL2 k, frobTwistGL τ k p e Q (rootSL2 τ k β A) =
      rootSL2 τ k (ω • β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A)) (m : ℕ) :
    ∀ β ∈ Δ, ∀ A : SL2 k, (frobTwistGL τ k p e Q)^[m] (rootSL2 τ k β A) =
      rootSL2 τ k (ω ^ m • β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p (e * m)) A) := by
  induction m with
  | zero =>
    intro β _ A
    rw [Function.iterate_zero_apply, pow_zero, one_smul, mul_zero, iterateFrobenius_zero]
    congr 1
  | succ m ih =>
    intro β hβ A
    rw [Function.iterate_succ_apply', ih β hβ A, hpin _ (pow_smul_mem_of_forall hΔ m β hβ),
      pow_succ', mul_smul, show e * (m + 1) = e * m + e by ring,
      ← iterateFrobenius_comp_iterateFrobenius]
    congr 1

variable (τ k) in
theorem ordinary_positive_toral_twist_pinning_normalization
    (hp : p ≠ 2) (e : ℕ) (he : 1 ≤ e)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (ω : WeylGroup τ)
    (hω : ω ∈ kernelPosStabilizer χ) :
    ∃ h ∈ torusGroup τ k,
      (∀ β ∈ unionSimpleRoots χ Set.univ, ∀ A : SL2 k,
        frobTwistGL τ k p e (h * canonicalRep (coxeterSystem τ) k ω) (rootSL2 τ k β A) =
          rootSL2 τ k (ω • β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A)) ∧
      (rootSpan τ k (kernelRoots χ)).map
          (frobTwistGL τ k p e (h * canonicalRep (coxeterSystem τ) k ω)) =
        rootSpan τ k (kernelRoots χ) ∧
      (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)).map
          (frobTwistGL τ k p e (h * canonicalRep (coxeterSystem τ) k ω)) =
        torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) ∧
      (∀ d : ℕ, 1 ≤ d → (∀ β ∈ unionSimpleRoots χ Set.univ, ω ^ d • β = β) →
        ∀ s ∈ rootSpan τ k (kernelRoots χ),
          (frobTwistGL τ k p e (h * canonicalRep (coxeterSystem τ) k ω))^[d] s =
            entrywiseFrobGL τ k p (e * d) s) ∧
      Finite (fixedPointsIn (rootSpan τ k (kernelRoots χ))
        (frobTwistGL τ k p e (h * canonicalRep (coxeterSystem τ) k ω))) ∧
      ∃ u ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ),
        (fixedPointsIn (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ))
            (frobTwistGL τ k p e (h * canonicalRep (coxeterSystem τ) k ω))).map
              (MulAut.conj u).toMonoidHom =
          fixedPointsIn (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ))
            (frobTwistGL τ k p e (canonicalRep (coxeterSystem τ) k ω)) := by
  classical
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  set n := canonicalRep (coxeterSystem τ) k ω with hn_def
  set Δ := simpleRoots (kernelRoots χ) with hΔ_def
  have hΔeq : unionSimpleRoots χ Set.univ = (Δ : Set (Fin τ.rank → ℤ)) :=
    unionSimpleRoots_univ_eq
  have hnN : n ∈ monomialSubgroup τ k := canonicalRep_mem_monomialSubgroup k ω
  have hπn : weylQuotientHom τ k ⟨n, hnN⟩ = ω :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep ω)
  have hωΔ : ∀ β ∈ Δ, ω • β ∈ Δ := fun β hβ => smul_mem_simpleRoots_kernelRoots hω hβ
  have hsign : ∀ β : Fin τ.rank → ℤ, ∃ a : kˣ, β ∈ Δ → ∀ c : k,
      frobTwistGL τ k p e n (rootSL2 τ k β (uSL c)) =
          rootSL2 τ k (ω • β) (uSL ((a : k) * iterateFrobenius k p e c)) ∧
        frobTwistGL τ k p e n (rootSL2 τ k β (vSL c)) =
          rootSL2 τ k (ω • β) (vSL (((a⁻¹ : kˣ) : k) * iterateFrobenius k p e c)) := by
    intro β
    by_cases hβ : β ∈ Δ
    · obtain ⟨a, ha⟩ := exists_frobTwistGL_rootSL2 p hp e hnN (simpleRoots_isRoot hβ)
      rw [hπn] at ha
      exact ⟨a, fun _ => ha⟩
    · exact ⟨1, fun h => absurd h hβ⟩
  choose a ha using hsign
  let ν : Fin Δ.card → Fin τ.rank → ℤ := fun i => (Δ.equivFin.symm i : Fin τ.rank → ℤ)
  have hνinj : Function.Injective ν := Subtype.val_injective.comp Δ.equivFin.symm.injective
  have hνΔ : ∀ i, ν i ∈ Δ := fun i => (Δ.equivFin.symm i).2
  obtain ⟨c, hc⟩ := algebraically_closed_lattice_character_interpolation k τ.rank Δ.card ν
    (linearIndependent_simpleRoots_kernelRoots hνinj hνΔ) fun i => (a (ω⁻¹ • ν i))⁻¹
  have hχc : ∀ β ∈ Δ, rootChar c (ω • β) = (a β)⁻¹ := by
    intro β hβ
    have hi := hc (Δ.equivFin ⟨ω • β, hωΔ β hβ⟩)
    have hν : ν (Δ.equivFin ⟨ω • β, hωΔ β hβ⟩) = ω • β := by
      simp only [ν, Equiv.symm_apply_apply]
    rw [hν, inv_smul_smul] at hi
    exact hi
  set h := rootDiagUnit τ c with hh_def
  have hhT : h ∈ torusGroup τ k := rootDiagUnit_mem_torusGroup c
  have hFh : ∀ y, frobTwistGL τ k p e (h * n) y = h * frobTwistGL τ k p e n y * h⁻¹ := by
    intro y
    simp only [frobTwistGL_apply]
    group
  have hpin : ∀ β ∈ Δ, ∀ A : SL2 k, frobTwistGL τ k p e (h * n) (rootSL2 τ k β A) =
      rootSL2 τ k (ω • β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A) := by
    intro β hβ A
    have hωβ : IsRoot τ (ω • β) := IsRoot.smul (simpleRoots_isRoot hβ) ω
    have heq := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := k))
      (f := (frobTwistGL τ k p e (h * n)).comp (rootSL2 τ k β))
      (g := (rootSL2 τ k (ω • β)).comp
        (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e))) ?_
    · exact DFunLike.congr_fun heq A
    rintro _ (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · change frobTwistGL τ k p e (h * n) (rootSL2 τ k β (uSL z)) =
        rootSL2 τ k (ω • β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) (uSL z))
      rw [hFh, (ha β hβ z).1, (rootDiagUnit_conj_rootSL2 c hωβ _).1, map_uSL, hχc β hβ,
        ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · change frobTwistGL τ k p e (h * n) (rootSL2 τ k β (vSL z)) =
        rootSL2 τ k (ω • β) (Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) (vSL z))
      rw [hFh, (ha β hβ z).2, (rootDiagUnit_conj_rootSL2 c hωβ _).2, map_vSL, hχc β hβ,
        inv_inv, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hhnN : h * n ∈ monomialSubgroup τ k := mul_mem (torusGroup_le_monomialSubgroup hhT) hnN
  have hπhn : weylQuotientHom τ k ⟨h * n, hhnN⟩ = ω := weylQuotientHom_eq (by
    simpa using (mapsRootLines_of_mem_torusGroup hhT).mul (mapsRootLines_canonicalRep ω))
  have hnT : n ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) :=
    canonicalRep_mem_normalizer ω
  have hhnT : h * n ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) :=
    mul_mem (Subgroup.le_normalizer hhT) hnT
  have hωχ : ω ∈ charStabilizer χ := hω.1
  have hS := map_frobTwistGL_rootSpan_kernelRoots p e hhnN (by rw [hπhn]; exact hωχ)
  have hM := map_frobTwistGL_torusGroup_sup_rootSpan p e hhnN hhnT (by rw [hπhn]; exact hωχ)
  have hiter : ∀ d : ℕ, (∀ β ∈ Δ, ω ^ d • β = β) → ∀ s ∈ rootSpan τ k (kernelRoots χ),
      (frobTwistGL τ k p e (h * n))^[d] s = entrywiseFrobGL τ k p (e * d) s := by
    intro d hd s hs
    let Fd : Monoid.End (ModGL τ k) := frobTwistGL τ k p e (h * n)
    have hFd : ⇑(Fd ^ d) = (⇑(frobTwistGL τ k p e (h * n)))^[d] := Monoid.End.coe_pow _ Fd d
    have hle : rootSpan τ k (kernelRoots χ) ≤
        MonoidHom.eqLocus (M := ModGL τ k) (Fd ^ d) (entrywiseFrobGL τ k p (e * d)) := by
      rw [rootSpan_kernelRoots_eq_iSup_rootRankOneGroup]
      refine iSup₂_le fun β hβ => ?_
      rintro _ ⟨A, rfl⟩
      change (Fd ^ d) (rootSL2 τ k β A) = entrywiseFrobGL τ k p (e * d) (rootSL2 τ k β A)
      rw [hFd, iterate_frobTwistGL_rootSL2 p e hωΔ hpin d β hβ A, hd β hβ,
        entrywiseFrobGL_rootSL2 p (e * d) (simpleRoots_isRoot hβ)]
    have h1 := hle hs
    change (Fd ^ d) s = _ at h1
    rwa [hFd] at h1
  have hfin : Finite (fixedPointsIn (rootSpan τ k (kernelRoots χ))
      (frobTwistGL τ k p e (h * n))) := by
    have hd : 1 ≤ orderOf ω := orderOf_pos ω
    have hsub : (fixedPointsIn (rootSpan τ k (kernelRoots χ)) (frobTwistGL τ k p e (h * n)) :
        Set (ModGL τ k)) ⊆ {g | entrywiseFrobGL τ k p (e * orderOf ω) g = g} := by
      intro s hs
      obtain ⟨hsS, hsF⟩ := mem_fixedPointsIn.1 hs
      have h1 := hiter (orderOf ω) (fun β _ => by rw [pow_orderOf_eq_one, one_smul]) s hsS
      rw [Function.iterate_fixed hsF] at h1
      exact h1.symm
    exact ((finite_setOf_entrywiseFrobGL_eq p (Nat.mul_le_mul he hd)).subset hsub).to_subtype
  have hker := rootCharKernel_signCharTuple (k := k) hk χ
  obtain ⟨-, ⟨hMc, -, hMsm, -, -⟩, -⟩ := exceptional_toral_centralizer_identity_component τ k hk
    (signCharTuple χ) (signCharTuple_sign χ)
  have hgroup : toralRootGroup τ k (signCharTuple χ) =
      torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) := by
    dsimp only [toralRootGroup]
    rw [hker]
  change IsConnectedAlgebraicSubgroup k
    ((toralRootGroup τ k (signCharTuple χ)).map (modGLPoint τ k).toMonoidHom) at hMc
  change Algebra.Smooth k (GLCoord k (Label τ) ⧸
    subgroupIdeal ((toralRootGroup τ k (signCharTuple χ)).map
      (modGLPoint τ k).toMonoidHom)) at hMsm
  rw [hgroup] at hMc hMsm
  have hF₀M : ∀ g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ),
      frobTwistGL τ k p e n g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) := by
    intro g hg
    rw [← map_frobTwistGL_torusGroup_sup_rootSpan p e hnN hnT (by rw [hπn]; exact hωχ)]
    exact ⟨g, hg, rfl⟩
  obtain ⟨u, huM, hu⟩ := exists_eq_inv_mul_frobTwistGL p he n hMc hMsm hF₀M
    (Subgroup.mem_sup_left hhT)
  have hF₀u : frobTwistGL τ k p e n u = u * h := by
    rw [hu]
    group
  have hconj : ∀ y, frobTwistGL τ k p e n (u * y * u⁻¹) =
      u * frobTwistGL τ k p e (h * n) y * u⁻¹ := by
    intro y
    rw [map_mul, map_mul, map_inv, hF₀u, hFh]
    group
  have hΔ' : ∀ β ∈ unionSimpleRoots χ Set.univ, β ∈ Δ := fun β hβ => by
    rw [← Finset.mem_coe, ← hΔeq]
    exact hβ
  refine ⟨h, hhT, fun β hβ A => hpin β (hΔ' β hβ) A, hS, hM,
    fun d _ hd => hiter d fun β hβ => hd β (by rw [hΔeq]; exact hβ), hfin, u, huM, ?_⟩
  ext z
  rw [Subgroup.mem_map, mem_fixedPointsIn]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyM, hyF⟩ := mem_fixedPointsIn.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ⟨mul_mem (mul_mem huM hyM) (inv_mem huM), by rw [hconj, hyF]⟩
  · rintro ⟨hzM, hzF⟩
    refine ⟨u⁻¹ * z * u, mem_fixedPointsIn.2 ⟨mul_mem (mul_mem (inv_mem huM) hzM) huM, ?_⟩, ?_⟩
    · have h1 := hconj (u⁻¹ * z * u)
      rw [show u * (u⁻¹ * z * u) * u⁻¹ = z by group, hzF] at h1
      calc frobTwistGL τ k p e (h * n) (u⁻¹ * z * u) =
          u⁻¹ * (u * frobTwistGL τ k p e (h * n) (u⁻¹ * z * u) * u⁻¹) * u := by group
        _ = u⁻¹ * z * u := by rw [← h1]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

end Main

end CFSG.LieType.AlgebraicGroups
