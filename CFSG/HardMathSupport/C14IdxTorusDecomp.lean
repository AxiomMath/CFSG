module

public import CFSG.HardMathSupport.C14IdxFixedBruhat
public import CFSG.LieType.Chevalley.FoldedWeylOrbits

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_fixed_torus_mul_mem_closure
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)} {e : ℕ}
    {Q : ModGL τ L} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hQX : ∀ α, IsRoot τ α → ∀ c : L, Q * pinnedX τ L α c * Q⁻¹ = pinnedX τ L (θ α) c)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hQ : (adjointGroup τ L).map (MulAut.conj Q).toMonoidHom = adjointGroup τ L)
    (hΨ : Set.BijOn θ (unionRoots χ J) (unionRoots χ J))
    (hΨp : Set.BijOn θ (posRoots (unionRoots χ J)) (posRoots (unionRoots χ J)))
    {s : ModGL τ L} (hs : s ∈ unionRootSpan L χ J) (hσ : frobTwistGL τ L 2 e Q s = s) :
    ∃ t ∈ unionTorus L χ J, frobTwistGL τ L 2 e Q t = t ∧
      t⁻¹ * s ∈ Subgroup.closure {x : ModGL τ L | x ∈ unionRootSpan L χ J ∧
        frobTwistGL τ L 2 e Q x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  classical
  let D : Subgroup (ModGL τ L) := Subgroup.closure {x : ModGL τ L |
    x ∈ unionRootSpan L χ J ∧ frobTwistGL τ L 2 e Q x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
  obtain ⟨w, hw, hwθ, t, ht, htfix, u, hu, hufix, v, hv, hvfix, hst⟩ :=
    exists_fixed_bruhat_factor hθ hQX hQT hQ hΨ hΨp hs hσ
  have hU2 : IsPGroup 2 (posUnipotent τ L) :=
    isPGroup_of_le_posFiltration (K := L) 2 Label.position_lt_card
      (posUnipotent_le_posFiltration τ L)
  have hpow : ∀ x ∈ unionUnipotent L χ J, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hU2 ⟨x, unionUnipotent_le_posUnipotent hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hmemD : ∀ x ∈ unionRootSpan L χ J, frobTwistGL τ L 2 e Q x = x →
      (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ D := by
    intro x hx hfx hx2
    exact Subgroup.subset_closure ⟨hx, hfx, hx2⟩
  have huD : u ∈ D := hmemD u (unionUnipotent_le_unionRootSpan hu) hufix (hpow u hu)
  have hvD : v ∈ D := hmemD v (unionUnipotent_le_unionRootSpan hv) hvfix (hpow v hv)
  have hθref : ∀ γ ∈ unionRoots χ J, ∀ α ∈ unionRoots χ J,
      θ (rootReflection γ • α) = rootReflection (θ γ) • θ α := by
    intro γ hγ α hα
    have hγr := isRoot_of_mem_unionRoots hγ
    have hθγ : IsRoot τ (θ γ) := isRoot_of_mem_unionRoots (hΨ.mapsTo hγ)
    rw [rootReflection_smul hγr, rootReflection_smul hθγ]
    have hc : corootPair (θ γ) (θ α) = corootPair γ α := by
      unfold corootPair
      rw [hθ γ α, hθ γ γ]
    simp only [map_sub, map_zsmul, hc]
  have hF : ∀ α ∈ unionRoots χ J,
      frobTwistGL τ L 2 e Q (pinnedX τ L α 1) = pinnedX τ L (θ α) 1 := by
    intro α hα
    rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX, iterateFrobenius_def, one_pow,
      hQX α (isRoot_of_mem_unionRoots hα) 1]
  have hπΔ : Set.MapsTo θ (unionSimpleRoots χ J) (unionSimpleRoots χ J) := by
    have h := (bijOn_simpleRoots_of_bijOn_posRoots
      (fun α hα => isRoot_of_mem_unionRoots hα) hΨ hΨp).mapsTo
    rwa [show (simpleRoots (unionRoots χ J) : Set _) = unionSimpleRoots χ J from
      Set.ext fun β => mem_simpleRoots_unionRoots_iff] at h
  have hπpos : ∀ α ∈ unionRoots χ J, 0 < height α → 0 < height (θ α) :=
    fun α hα hpos => (hΨp.mapsTo ⟨hα, hpos⟩).2
  let φ : WeylGroup τ →* ModGL τ L :=
    { toFun := canonicalRep (coxeterSystem τ) L
      map_one' := canonicalRep_one _ _
      map_mul' := CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo }
  have hXsub : φ '' {v : WeylGroup τ | v ∈ unionWeylGroup χ J ∧
      (∀ α ∈ unionRoots χ J, θ (v • α) = v • θ α) ∧ v * v = 1} ⊆
      {x : ModGL τ L | x ∈ unionRootSpan L χ J ∧ frobTwistGL τ L 2 e Q x = x ∧
        ∃ k : ℕ, x ^ 2 ^ k = 1} := by
    rintro _ ⟨x, ⟨hxw, hxθ, hx2⟩, rfl⟩
    have hφx : φ x = canonicalRep (coxeterSystem τ) L x := rfl
    rw [hφx]
    refine ⟨canonicalRep_mem_rootSpan_unionRoots hxw, ?_, ?_⟩
    · exact map_canonicalRep_eq_self_of_commute (frobTwistGL τ L 2 e Q) θ hΨ hθref hF hxw hxθ
    · exact ⟨1, by
        simpa [pow_two] using CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_self_charTwo hx2⟩
  have hwD : w ∈ Subgroup.closure {v : WeylGroup τ | v ∈ unionWeylGroup χ J ∧
      (∀ α ∈ unionRoots χ J, θ (v • α) = v • θ α) ∧ v * v = 1} :=
    mem_closure_fixed_involutions θ hΨ hπΔ hπpos hθref hw hwθ
  have hnwD : φ w ∈ D := by
    have h1 : φ w ∈ (Subgroup.closure {v : WeylGroup τ | v ∈ unionWeylGroup χ J ∧
        (∀ α ∈ unionRoots χ J, θ (v • α) = v • θ α) ∧ v * v = 1}).map φ :=
      Subgroup.mem_map_of_mem φ hwD
    rw [MonoidHom.map_closure] at h1
    exact Subgroup.closure_mono hXsub h1
  refine ⟨t, ht, htfix, ?_⟩
  have hcalc : t⁻¹ * s = u * canonicalRep (coxeterSystem τ) L w * v := by
    rw [hst]
    group
  rw [hcalc]
  exact mul_mem (mul_mem huD hnwD) hvD

end CFSG.HardMathSupport.C14Idx
