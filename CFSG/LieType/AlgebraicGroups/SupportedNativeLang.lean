module

public import CFSG.LieType.AlgebraicGroups.SeminaireExp3
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.LieType.Chevalley.TwistMap
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv Pointwise

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k]

variable (τ k) in
@[expose] def modGLZariski
    : ModGL τ k ≃* SeminaireExp3.ZariskiGL (Label τ) k :=
  (modGLEquivGL τ k).trans SeminaireExp3.ZariskiGL.toGL.symm

theorem pt_modGLZariski (g : ModGL τ k) :
    SeminaireExp3.ZariskiGL.pt (modGLZariski τ k g) = (modGLPoint τ k g).ofConv :=
  rfl

theorem transportPoints_eq_image_modGLZariski (S : Set (ModGL τ k)) :
    transportPoints (modGLPoint τ k) S =
      SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k '' S) := by
  rw [Set.image_image]
  rfl

theorem isDomainImage_letterCurve
    [IsAlgClosed k] (l : Letter τ) :
    SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k '' Set.range (letterUnit τ k l))) := by
  have hbc : ∀ z : Polynomial k →ₐ[k] k,
      z.comp (unitCo k (letterUnit τ (Polynomial k) l Polynomial.X)) =
        (modGLPoint τ k (letterUnit τ k l (z Polynomial.X))).ofConv := fun z =>
    comp_unitCo_of_baseChange z (letterUnit τ (Polynomial k) l Polynomial.X)
      (letterUnit τ k l (z Polynomial.X)) (baseChange_letterUnit _ l Polynomial.X)
  refine ⟨Polynomial k, inferInstance, inferInstance, inferInstance, inferInstance,
    unitCo k (letterUnit τ (Polynomial k) l Polynomial.X), ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩
    refine ⟨Polynomial.aeval c, ?_⟩
    show (Polynomial.aeval c).comp _ = _
    rw [hbc, Polynomial.aeval_X, pt_modGLZariski]
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨_, ⟨z Polynomial.X, rfl⟩, rfl⟩, by rw [pt_modGLZariski]; exact (hbc z).symm⟩

variable (τ k) in
abbrev subsystemPointSubgroup
    (J : Set (Fin τ.rank)) :
    Subgroup (WithConv (GLCoord k (Label τ) →ₐ[k] k)) :=
  (subsystemGroup τ k J).map (modGLPoint τ k).toMonoidHom

variable (τ k) in
abbrev supportedCurve
    (J : Set (Fin τ.rank)) (l : {l : Letter τ // l.1 ∈ J}) :
    Set (SeminaireExp3.ZariskiGL (Label τ) k) :=
  modGLZariski τ k '' Set.range (letterUnit τ k l.1)

theorem map_subsystemGroup_eq_closure
    (J : Set (Fin τ.rank)) :
    (subsystemGroup τ k J).map (modGLZariski τ k).toMonoidHom =
      Subgroup.closure (⋃ l, supportedCurve τ k J l) := by
  rw [subsystemGroup, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨i, hi, c, rfl | rfl⟩, rfl⟩
    · exact ⟨⟨(i, true), hi⟩, _, ⟨c, rfl⟩, rfl⟩
    · exact ⟨⟨(i, false), hi⟩, _, ⟨c, rfl⟩, rfl⟩
  · rintro ⟨⟨⟨i, b⟩, hi⟩, _, ⟨c, rfl⟩, rfl⟩
    refine ⟨letterUnit τ k (i, b) c, ⟨i, hi, c, ?_⟩, rfl⟩
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem supported_realization
    [IsAlgClosed k] (J : Set (Fin τ.rank)) :
    IsPointClosed k (transportPoints (modGLPoint τ k) (subsystemGroup τ k J : Set (ModGL τ k))) ∧
      IsConnectedAlgebraicSubgroup k (subsystemPointSubgroup τ k J) ∧
      Algebra.Smooth k (GLCoord k (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ k J)) ∧
      IrreducibleSpace
        (PrimeSpectrum (GLCoord k (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ k J))) ∧
      ∃ e : WithConv ((GLCoord k (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ k J)) →ₐ[k]
          k) ≃* subsystemGroup τ k J, ∀ φ,
        ((e φ : subsystemGroup τ k J) : ModGL τ k) =
          (modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) := by
  have hW : ∀ l, SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' supportedCurve τ k J l) :=
    fun l => isDomainImage_letterCurve l.1
  have h1 : ∀ l, (1 : SeminaireExp3.ZariskiGL (Label τ) k) ∈ supportedCurve τ k J l :=
    fun l => ⟨1, ⟨0, letterUnit_zero l.1⟩, map_one _⟩
  obtain ⟨-, -, a, ha⟩ := SeminaireExp3.ZariskiGL.closure_eq_wordSet (supportedCurve τ k J) hW h1
  have hdom : SeminaireExp3.IsDomainImage k
      (transportPoints (modGLPoint τ k) (subsystemGroup τ k J : Set (ModGL τ k))) := by
    have himg : modGLZariski τ k '' (subsystemGroup τ k J : Set (ModGL τ k)) =
        SeminaireExp3.ZariskiGL.wordSet (supportedCurve τ k J) a := by
      rw [← ha, ← map_subsystemGroup_eq_closure, Subgroup.coe_map]
      rfl
    rw [transportPoints_eq_image_modGLZariski, himg]
    exact SeminaireExp3.ZariskiGL.isDomainImage_wordSet _ hW a
  obtain ⟨hcl, h, he⟩ := isConnectedAlgebraicSubgroup_map (modGLPoint τ k) (subsystemGroup τ k J)
    hdom.isPointConstructible hdom.isPointIrreducible
  obtain ⟨hsm, -, hirrsp⟩ := h.smooth
  exact ⟨hcl, h, hsm, hirrsp, he⟩

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem entrywiseFrobGL_letterUnit
    (e : ℕ) (l : Letter τ) (c : k) :
    entrywiseFrobGL τ k p e (letterUnit τ k l c) = letterUnit τ k l (c ^ p ^ e) := by
  unfold letterUnit
  split_ifs
  · refine Units.ext ?_
    rw [Units.coe_map, coe_xUnit, coe_xUnit]
    exact (entrywise_xOp (iterateFrobenius k p e) l.1 c).trans (by rw [iterateFrobenius_def])
  · refine Units.ext ?_
    rw [Units.coe_map, coe_yUnit, coe_yUnit]
    exact (entrywise_yOp (iterateFrobenius k p e) l.1 c).trans (by rw [iterateFrobenius_def])

theorem map_entrywiseFrobGL_subsystemGroup
    [IsAlgClosed k] (e : ℕ) (J : Set (Fin τ.rank)) :
    (subsystemGroup τ k J).map (entrywiseFrobGL τ k p e) = subsystemGroup τ k J := by
  rw [subsystemGroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨i, hi, c, rfl | rfl⟩, rfl⟩
    · exact ⟨i, hi, c ^ p ^ e, Or.inl (entrywiseFrobGL_letterUnit p e (i, true) c)⟩
    · exact ⟨i, hi, c ^ p ^ e, Or.inr (entrywiseFrobGL_letterUnit p e (i, false) c)⟩
  · rintro ⟨i, hi, c, rfl | rfl⟩
    · set c' := (iterateFrobeniusEquiv k p e).symm c
      have hc : c' ^ p ^ e = c := by
        rw [← iterateFrobenius_def, ← coe_iterateFrobeniusEquiv, RingEquiv.apply_symm_apply]
      exact ⟨xUnit τ k i c', ⟨i, hi, c', Or.inl rfl⟩,
        (entrywiseFrobGL_letterUnit p e (i, true) c').trans (by rw [hc]; rfl)⟩
    · set c' := (iterateFrobeniusEquiv k p e).symm c
      have hc : c' ^ p ^ e = c := by
        rw [← iterateFrobenius_def, ← coe_iterateFrobeniusEquiv, RingEquiv.apply_symm_apply]
      exact ⟨yUnit τ k i c', ⟨i, hi, c', Or.inr rfl⟩,
        (entrywiseFrobGL_letterUnit p e (i, false) c').trans (by rw [hc]; rfl)⟩

theorem map_frobTwistGL_subsystemGroup
    [IsAlgClosed k] (e : ℕ) {J : Set (Fin τ.rank)}
    {A : ModGL τ k} (hA : A ∈ Subgroup.normalizer (subsystemGroup τ k J : Set (ModGL τ k))) :
    (subsystemGroup τ k J).map (frobTwistGL τ k p e A) = subsystemGroup τ k J := by
  rw [frobTwistGL, ← Subgroup.map_map, map_entrywiseFrobGL_subsystemGroup,
    map_conj_eq_of_mem_normalizer hA]

@[expose] def supportedFrobTwistAut
    [IsAlgClosed k] (e : ℕ) {J : Set (Fin τ.rank)}
    {A : ModGL τ k} (hA : A ∈ Subgroup.normalizer (subsystemGroup τ k J : Set (ModGL τ k))) :
    MulAut (subsystemGroup τ k J) :=
  ((subsystemGroup τ k J).equivMapOfInjective (frobTwistGL τ k p e A)
    (frobTwistGL_injective p e A)).trans
      (MulEquiv.subgroupCongr (map_frobTwistGL_subsystemGroup p e hA))

theorem coe_supportedFrobTwistAut
    [IsAlgClosed k] (e : ℕ) {J : Set (Fin τ.rank)}
    {A : ModGL τ k} (hA : A ∈ Subgroup.normalizer (subsystemGroup τ k J : Set (ModGL τ k)))
    (g : subsystemGroup τ k J) :
    (supportedFrobTwistAut p e hA g : ModGL τ k) = frobTwistGL τ k p e A g :=
  rfl

end Frobenius


theorem supported_native_affine_realization_and_Lang
    (τ : Tag) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] (J : Set (Fin τ.rank)) :
    (IsPointClosed Ω
        (transportPoints (modGLPoint τ Ω) (subsystemGroup τ Ω J : Set (ModGL τ Ω))) ∧
      IsConnectedAlgebraicSubgroup Ω (subsystemPointSubgroup τ Ω J) ∧
      Algebra.Smooth Ω (GLCoord Ω (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ Ω J)) ∧
      IrreducibleSpace
        (PrimeSpectrum (GLCoord Ω (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ Ω J))) ∧
      ∃ e : WithConv ((GLCoord Ω (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ Ω J)) →ₐ[Ω]
          Ω) ≃* subsystemGroup τ Ω J, ∀ φ,
        ((e φ : subsystemGroup τ Ω J) : ModGL τ Ω) =
          (modGLPoint τ Ω).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ Ω _)))) ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] [CharP Ω ℓ] (f : ℕ), 1 ≤ f →
      ∀ A ∈ Subgroup.normalizer (subsystemGroup τ Ω J : Set (ModGL τ Ω)),
        (∃ Ψ : MulAut (subsystemGroup τ Ω J), ∀ g,
          (Ψ g : ModGL τ Ω) = frobTwistGL τ Ω ℓ f A g) ∧
        (∃ σ : (GLCoord Ω (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ Ω J)) →ₐc[Ω]
            (GLCoord Ω (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ Ω J)),
          (∀ φ, (modGLPoint τ Ω).symm (toConv ((pointMap σ φ).ofConv.comp
              (Ideal.Quotient.mkₐ Ω _))) =
            frobTwistGL τ Ω ℓ f A
              ((modGLPoint τ Ω).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ Ω _))))) ∧
          ∀ D ∈ tangentSpace Ω _ (Bialgebra.counitAlgHom Ω
              (GLCoord Ω (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ Ω J))),
            D ∘ₗ (σ : (GLCoord Ω (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ Ω J)) →ₐ[Ω]
              (GLCoord Ω (Label τ) ⧸ subgroupIdeal (subsystemPointSubgroup τ Ω J))).toLinearMap =
                0) ∧
        (∀ y ∈ subsystemGroup τ Ω J, ∃ h ∈ subsystemGroup τ Ω J,
          y = h⁻¹ * frobTwistGL τ Ω ℓ f A h) ∧
        ∀ y ∈ subsystemGroup τ Ω J, ∃ h ∈ subsystemGroup τ Ω J, ∀ g : ModGL τ Ω,
          y * frobTwistGL τ Ω ℓ f A g * y⁻¹ = h⁻¹ * frobTwistGL τ Ω ℓ f A (h * g * h⁻¹) * h := by
  obtain ⟨hcl, hZ, hsm, hirr, he⟩ := supported_realization (τ := τ) (k := Ω) J
  refine ⟨⟨hcl, hZ, hsm, hirr, he⟩, fun ℓ _ _ f hf A hA => ?_⟩
  have hQ : ∀ g ∈ subsystemGroup τ Ω J, frobTwistGL τ Ω ℓ f A g ∈ subsystemGroup τ Ω J :=
    fun g hg => by
      rw [← map_frobTwistGL_subsystemGroup ℓ f hA]
      exact ⟨g, hg, rfl⟩
  obtain ⟨σ, hpt, hzero, hlang⟩ := exists_frobTwist_restriction ℓ hZ hf A hQ
  have hlang' : ∀ y ∈ subsystemGroup τ Ω J, ∃ h ∈ subsystemGroup τ Ω J,
      y = h⁻¹ * frobTwistGL τ Ω ℓ f A h := fun y hy => by
    obtain ⟨h, hh, hhy⟩ := hlang y hy
    exact ⟨h, hh, hhy.symm⟩
  refine ⟨⟨supportedFrobTwistAut ℓ f hA, coe_supportedFrobTwistAut ℓ f hA⟩, ⟨σ, hpt, hzero⟩,
    hlang', fun y hy => ?_⟩
  obtain ⟨h, hh, rfl⟩ := hlang' y hy
  refine ⟨h, hh, fun g => ?_⟩
  rw [map_mul, map_mul, map_inv]
  group

theorem E7_supported_native_affine_realization_and_Lang
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (J : Set (Fin Tag.E7.rank)) :
    (IsPointClosed Ω (transportPoints (modGLPoint Tag.E7 Ω)
        (subsystemGroup Tag.E7 Ω J : Set (ModGL Tag.E7 Ω))) ∧
      IsConnectedAlgebraicSubgroup Ω (subsystemPointSubgroup Tag.E7 Ω J) ∧
      Algebra.Smooth Ω
        (GLCoord Ω (Label Tag.E7) ⧸ subgroupIdeal (subsystemPointSubgroup Tag.E7 Ω J)) ∧
      IrreducibleSpace (PrimeSpectrum
        (GLCoord Ω (Label Tag.E7) ⧸ subgroupIdeal (subsystemPointSubgroup Tag.E7 Ω J))) ∧
      ∃ e : WithConv ((GLCoord Ω (Label Tag.E7) ⧸
          subgroupIdeal (subsystemPointSubgroup Tag.E7 Ω J)) →ₐ[Ω] Ω) ≃*
            subsystemGroup Tag.E7 Ω J, ∀ φ,
        ((e φ : subsystemGroup Tag.E7 Ω J) : ModGL Tag.E7 Ω) =
          (modGLPoint Tag.E7 Ω).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ Ω _)))) ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] [CharP Ω ℓ] (f : ℕ), 1 ≤ f →
      ∀ A ∈ Subgroup.normalizer (subsystemGroup Tag.E7 Ω J : Set (ModGL Tag.E7 Ω)),
        (∃ Ψ : MulAut (subsystemGroup Tag.E7 Ω J), ∀ g,
          (Ψ g : ModGL Tag.E7 Ω) = frobTwistGL Tag.E7 Ω ℓ f A g) ∧
        (∃ σ : (GLCoord Ω (Label Tag.E7) ⧸ subgroupIdeal (subsystemPointSubgroup Tag.E7 Ω J))
            →ₐc[Ω]
            (GLCoord Ω (Label Tag.E7) ⧸ subgroupIdeal (subsystemPointSubgroup Tag.E7 Ω J)),
          (∀ φ, (modGLPoint Tag.E7 Ω).symm (toConv ((pointMap σ φ).ofConv.comp
              (Ideal.Quotient.mkₐ Ω _))) =
            frobTwistGL Tag.E7 Ω ℓ f A
              ((modGLPoint Tag.E7 Ω).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ Ω _))))) ∧
          ∀ D ∈ tangentSpace Ω _ (Bialgebra.counitAlgHom Ω
              (GLCoord Ω (Label Tag.E7) ⧸ subgroupIdeal (subsystemPointSubgroup Tag.E7 Ω J))),
            D ∘ₗ (σ : (GLCoord Ω (Label Tag.E7) ⧸
                subgroupIdeal (subsystemPointSubgroup Tag.E7 Ω J)) →ₐ[Ω]
              (GLCoord Ω (Label Tag.E7) ⧸
                subgroupIdeal (subsystemPointSubgroup Tag.E7 Ω J))).toLinearMap = 0) ∧
        (∀ y ∈ subsystemGroup Tag.E7 Ω J, ∃ h ∈ subsystemGroup Tag.E7 Ω J,
          y = h⁻¹ * frobTwistGL Tag.E7 Ω ℓ f A h) ∧
        ∀ y ∈ subsystemGroup Tag.E7 Ω J, ∃ h ∈ subsystemGroup Tag.E7 Ω J,
          ∀ g : ModGL Tag.E7 Ω, y * frobTwistGL Tag.E7 Ω ℓ f A g * y⁻¹ =
            h⁻¹ * frobTwistGL Tag.E7 Ω ℓ f A (h * g * h⁻¹) * h :=
  supported_native_affine_realization_and_Lang Tag.E7 Ω J

end CFSG.LieType.AlgebraicGroups
