module

public import CFSG.LieType.AlgebraicGroups.G2ExceptionalProjection
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagram
public import CFSG.LieType.AlgebraicGroups.BijectiveTangentIsomorphism
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree WithConv TensorProduct

open scoped CFSG.ConvolutionPoints

section Points

variable {L : Type} [Field L] [CharP L 3]

theorem g2Exceptional_comp_self
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) :
    Φ.toMonoidHom.comp Φ.toMonoidHom = frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) := by
  refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
  · fin_cases i
    · show Φ (Φ (xElement ⟨0, by decide⟩ c)) =
        frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (xElement ⟨0, by decide⟩ c)
      rw [(hΦ c).1, (hΦ c).2.2.1, frobeniusTwist_xElement]
      simp only [iterateFrobenius_def, pow_one]
    · show Φ (Φ (xElement ⟨1, by decide⟩ c)) =
        frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (xElement ⟨1, by decide⟩ c)
      rw [(hΦ c).2.2.1, (hΦ (c ^ 3)).1, frobeniusTwist_xElement]
      simp only [iterateFrobenius_def, pow_one]
  · fin_cases i
    · show Φ (Φ (yElement ⟨0, by decide⟩ c)) =
        frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (yElement ⟨0, by decide⟩ c)
      rw [(hΦ c).2.1, (hΦ c).2.2.2, frobeniusTwist_yElement]
      simp only [iterateFrobenius_def, pow_one]
    · show Φ (Φ (yElement ⟨1, by decide⟩ c)) =
        frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (yElement ⟨1, by decide⟩ c)
      rw [(hΦ c).2.2.2, (hΦ (c ^ 3)).2.1, frobeniusTwist_yElement]
      simp only [iterateFrobenius_def, pow_one]

theorem g2Exceptional_comm_frobeniusTwist
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) :
    Φ.toMonoidHom.comp (frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1)) =
      (frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1)).comp Φ.toMonoidHom := by
  refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
  · fin_cases i
    · show Φ (frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (xElement ⟨0, by decide⟩ c)) =
        frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (Φ (xElement ⟨0, by decide⟩ c))
      rw [frobeniusTwist_xElement, (hΦ (iterateFrobenius L 3 1 c)).1, (hΦ c).1,
        frobeniusTwist_xElement]
    · show Φ (frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (xElement ⟨1, by decide⟩ c)) =
        frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (Φ (xElement ⟨1, by decide⟩ c))
      rw [frobeniusTwist_xElement, (hΦ (iterateFrobenius L 3 1 c)).2.2.1, (hΦ c).2.2.1,
        frobeniusTwist_xElement]
      simp only [iterateFrobenius_def, pow_one]
  · fin_cases i
    · show Φ (frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (yElement ⟨0, by decide⟩ c)) =
        frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (Φ (yElement ⟨0, by decide⟩ c))
      rw [frobeniusTwist_yElement, (hΦ (iterateFrobenius L 3 1 c)).2.1, (hΦ c).2.1,
        frobeniusTwist_yElement]
    · show Φ (frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (yElement ⟨1, by decide⟩ c)) =
        frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (Φ (yElement ⟨1, by decide⟩ c))
      rw [frobeniusTwist_yElement, (hΦ (iterateFrobenius L 3 1 c)).2.2.2, (hΦ c).2.2.2,
        frobeniusTwist_yElement]
      simp only [iterateFrobenius_def, pow_one]

end Points

section Second

variable {L : Type} [Field L] [IsAlgClosed L]

omit [IsAlgClosed L] in
theorem snd_modGLPairPoint_symm {τ : Tag} {M : ℕ}
    (y : WithConv (GLCoord L (Label τ) ⊗[L] GLCoord L (Fin M) →ₐ[L] L)) :
    ((modGLPairPoint τ L M).symm y).2 =
      glPointEquiv.symm (toConv (y.ofConv.comp Algebra.TensorProduct.includeRight)) :=
  rfl

@[expose] def g2GraphSndCoGL
    (Φ : MulAut (adjointGroup Tag.G2 L)) :
    GLCoord L (Label Tag.G2) →ₐ[L] g2GraphCoord L Φ :=
  ((Ideal.Quotient.mkₐ L _).comp Algebra.TensorProduct.includeRight).comp
    (glReindexCo g2LabelEquiv.symm)

theorem toConv_comp_g2GraphSndCoGL
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) (w : g2GraphCoord L Φ →ₐ[L] L) :
    toConv (w.comp (g2GraphSndCoGL Φ)) =
      modGLPoint Tag.G2 L (Φ (g2GraphPointEquiv hΦ (toConv w))) := by
  have h2 : glPointEquiv.symm (toConv ((w.comp (Ideal.Quotient.mkₐ L _)).comp
      Algebra.TensorProduct.includeRight)) = g2GraphHom Φ (g2GraphPointEquiv hΦ (toConv w)) :=
    congrArg Prod.snd (modGLPairPoint_symm_g2Graph hΦ (toConv w))
  have hm : ∀ g : ModGL Tag.G2 L,
      modGLPoint Tag.G2 L g = glPointEquiv (modGLEquivGL Tag.G2 L g) := fun _ => rfl
  apply glPointEquiv.symm.injective
  rw [g2GraphSndCoGL, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    glPointEquiv_symm_comp_glReindexCo, h2, g2GraphHom_apply, glReindex_symm_glReindex, hm,
    MulEquiv.symm_apply_apply]

theorem comp_g2GraphSndCoGL_mem
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) (w : g2GraphCoord L Φ →ₐ[L] L) :
    w.comp (g2GraphSndCoGL Φ) ∈ subgroupPoints (adjointPointSubgroup Tag.G2 L) := by
  rw [mem_subgroupPoints_adjointPointSubgroup, toConv_comp_g2GraphSndCoGL hΦ,
    MulEquiv.symm_apply_apply]
  exact (Φ _).2

@[expose] def g2GraphSndCo0
    {Φ : MulAut (adjointGroup Tag.G2 L)} (hΦ : IsG2Exceptional L Φ) :
    realizedCoord Tag.G2 L →ₐ[L] g2GraphCoord L Φ :=
  haveI := (g2Graph_realization hΦ).2.1.finiteType
  haveI := (g2Graph_realization hΦ).2.1.isReduced
  liftOfPoints _ (g2GraphSndCoGL Φ) (comp_g2GraphSndCoGL_mem hΦ)

theorem realizedPointEquiv_comp_g2GraphSndCo0
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) (w : WithConv (g2GraphCoord L Φ →ₐ[L] L)) :
    realizedPointEquiv Tag.G2 L (toConv (w.ofConv.comp (g2GraphSndCo0 hΦ))) =
      Φ (g2GraphPointEquiv hΦ w) := by
  have := (g2Graph_realization hΦ).2.1.finiteType
  have := (g2Graph_realization hΦ).2.1.isReduced
  have h : (g2GraphSndCo0 hΦ).comp (Ideal.Quotient.mkₐ L _) = g2GraphSndCoGL Φ :=
    liftOfPoints_comp_mkₐ _ _ _
  apply Subtype.ext
  rw [coe_realizedPointEquiv, ofConv_toConv, AlgHom.comp_assoc, h, toConv_comp_g2GraphSndCoGL hΦ,
    toConv_ofConv, MulEquiv.symm_apply_apply]

@[expose] def g2GraphSndCo
    {Φ : MulAut (adjointGroup Tag.G2 L)} (hΦ : IsG2Exceptional L Φ) :
    realizedCoord Tag.G2 L →ₐc[L] g2GraphCoord L Φ :=
  haveI := (g2Graph_realization hΦ).2.1.finiteType
  haveI := (g2Graph_realization hΦ).2.1.isReduced
  bialgHomOfPointMulTo (g2GraphSndCo0 hΦ) fun y z => by
    apply (realizedPointEquiv Tag.G2 L).injective
    rw [map_mul, realizedPointEquiv_comp_g2GraphSndCo0, realizedPointEquiv_comp_g2GraphSndCo0,
      realizedPointEquiv_comp_g2GraphSndCo0, map_mul, map_mul]

theorem realizedPointEquiv_comp_g2GraphSndCo
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) (w : WithConv (g2GraphCoord L Φ →ₐ[L] L)) :
    realizedPointEquiv Tag.G2 L
        (toConv (w.ofConv.comp (g2GraphSndCo hΦ : realizedCoord Tag.G2 L →ₐ[L] _))) =
      Φ (g2GraphPointEquiv hΦ w) :=
  realizedPointEquiv_comp_g2GraphSndCo0 hΦ w

end Second


theorem pointMap_mul {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]
    (σ₁ σ₂ : A →ₐc[k] A) (φ : WithConv (A →ₐ[k] k)) :
    pointMap (σ₁ * σ₂) φ = pointMap σ₂ (pointMap σ₁ φ) :=
  rfl

theorem exceptional_Lang_G2_exceptional_map_regularity
    (L : Type) [Field L] [IsAlgClosed L]
    [CharP L 3] (Φ : MulAut (adjointGroup Tag.G2 L)) (hΦ : IsG2Exceptional L Φ) :
    ∃ σ : realizedCoord Tag.G2 L →ₐc[L] realizedCoord Tag.G2 L,
      (∀ φ, realizedPointEquiv Tag.G2 L (pointMap σ φ) = Φ (realizedPointEquiv Tag.G2 L φ)) ∧
      (∀ σ' : realizedCoord Tag.G2 L →ₐc[L] realizedCoord Tag.G2 L,
        (∀ φ, realizedPointEquiv Tag.G2 L (pointMap σ' φ) = Φ (realizedPointEquiv Tag.G2 L φ)) →
          σ' = σ) ∧
      (∃ Fr : realizedCoord Tag.G2 L →ₐc[L] realizedCoord Tag.G2 L,
        ∀ φ, (realizedPointEquiv Tag.G2 L (pointMap Fr φ) : ModGL Tag.G2 L) =
          Units.map (entrywiseHom (iterateFrobenius L 3 1)) (realizedPointEquiv Tag.G2 L φ)) ∧
      ∀ Fr : realizedCoord Tag.G2 L →ₐc[L] realizedCoord Tag.G2 L,
        (∀ φ, (realizedPointEquiv Tag.G2 L (pointMap Fr φ) : ModGL Tag.G2 L) =
          Units.map (entrywiseHom (iterateFrobenius L 3 1)) (realizedPointEquiv Tag.G2 L φ)) →
        σ * σ = Fr ∧ σ * Fr = Fr * σ ∧
        ∀ a : ℕ, (Fr ^ a * σ) * (Fr ^ a * σ) = Fr ^ (2 * a + 1) ∧
          ∀ D ∈ tangentSpace L (realizedCoord Tag.G2 L) (Bialgebra.counitAlgHom L _),
            D ∘ₗ (((Fr ^ a * σ) * (Fr ^ a * σ) : realizedCoord Tag.G2 L →ₐc[L] _) :
              realizedCoord Tag.G2 L →ₐ[L] realizedCoord Tag.G2 L).toLinearMap = 0 := by
  have hG := isConnectedAlgebraicSubgroup_adjointPointSubgroup Tag.G2 L
  have hΓ := g2Graph_realization hΦ
  have := hG.finiteType
  have := hΓ.2.1.finiteType
  have := hΓ.2.2.1
  obtain ⟨-, -, -, hpt, htan, -, -⟩ :=
    exceptional_Lang_G2_exceptional_graph_tangent_projection L Φ hΦ
  obtain ⟨ψ, hψ, -⟩ := exceptional_Lang_bijective_tangent_group_map_isomorphism
    (g2GraphProjCo Φ) hpt htan
  have hdet : ∀ σ₁ σ₂ : realizedCoord Tag.G2 L →ₐc[L] realizedCoord Tag.G2 L,
      (∀ φ, realizedPointEquiv Tag.G2 L (pointMap σ₁ φ) =
        realizedPointEquiv Tag.G2 L (pointMap σ₂ φ)) → σ₁ = σ₂ := by
    intro σ₁ σ₂ h
    have h' : (σ₁ : realizedCoord Tag.G2 L →ₐ[L] realizedCoord Tag.G2 L) = σ₂ :=
      (exceptional_Lang_affine_point_and_product_geometry L).2.2.2.2.1 _ _ _ _ fun x =>
        congrArg ofConv ((realizedPointEquiv Tag.G2 L).injective (h (toConv x)))
    exact BialgHom.ext fun x => DFunLike.congr_fun h' x
  have hσ : ∀ φ, realizedPointEquiv Tag.G2 L (pointMap (ψ.comp (g2GraphSndCo hΦ)) φ) =
      Φ (realizedPointEquiv Tag.G2 L φ) := by
    intro φ
    have hw : g2GraphPointEquiv hΦ (toConv (φ.ofConv.comp (ψ : g2GraphCoord L Φ →ₐ[L] _))) =
        realizedPointEquiv Tag.G2 L φ := by
      rw [← realizedPointEquiv_comp_g2GraphProjCo hΦ, ofConv_toConv]
      congr 2
      exact AlgHom.ext fun x => congrArg φ.ofConv (DFunLike.congr_fun hψ x)
    rw [← hw, ← realizedPointEquiv_comp_g2GraphSndCo hΦ, ofConv_toConv]
    rfl
  obtain ⟨σF, hσF, hdF, -⟩ :=
    (exceptional_Lang_ordinary_Frobenius_diagram_morphisms 3 L).1 Tag.G2 1 le_rfl
  refine ⟨ψ.comp (g2GraphSndCo hΦ), hσ, fun σ' h => hdet _ _ fun φ => (h φ).trans (hσ φ).symm,
    ⟨σF, hσF⟩, fun Fr hFr => ?_⟩
  set σ := ψ.comp (g2GraphSndCo hΦ)
  have hFr' : ∀ φ, realizedPointEquiv Tag.G2 L (pointMap Fr φ) =
      frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) (realizedPointEquiv Tag.G2 L φ) :=
    fun φ => Subtype.ext (hFr φ)
  have hFrF : Fr = σF := hdet _ _ fun φ => Subtype.ext ((hFr φ).trans (hσF φ).symm)
  have hsq : σ * σ = Fr := hdet _ _ fun φ => by
    rw [pointMap_mul, hσ, hσ, hFr']
    exact DFunLike.congr_fun (g2Exceptional_comp_self hΦ) _
  have hcomm : σ * Fr = Fr * σ := hdet _ _ fun φ => by
    rw [pointMap_mul, pointMap_mul, hFr', hσ, hσ, hFr']
    exact (DFunLike.congr_fun (g2Exceptional_comm_frobeniusTwist hΦ) _).symm
  have hpow : ∀ a : ℕ, (Fr ^ a * σ) * (Fr ^ a * σ) = Fr ^ (2 * a + 1) := fun a => by
    have hc : σ * Fr ^ a = Fr ^ a * σ := (Commute.pow_right hcomm a).eq
    calc (Fr ^ a * σ) * (Fr ^ a * σ) = Fr ^ a * (σ * Fr ^ a) * σ := by
          simp only [mul_assoc]
      _ = Fr ^ a * (Fr ^ a * σ) * σ := by rw [hc]
      _ = Fr ^ (a + a) * (σ * σ) := by rw [pow_add]; simp only [mul_assoc]
      _ = Fr ^ (2 * a + 1) := by rw [hsq, ← pow_succ, two_mul]
  refine ⟨hsq, hcomm, fun a => ⟨hpow a, fun D hD => ?_⟩⟩
  rw [hpow, pow_succ', hFrF]
  change D ∘ₗ ((σF : realizedCoord Tag.G2 L →ₐ[L] _).comp
    ((σF ^ (2 * a) : realizedCoord Tag.G2 L →ₐc[L] _) :
      realizedCoord Tag.G2 L →ₐ[L] _)).toLinearMap = 0
  rw [AlgHom.comp_toLinearMap, ← LinearMap.comp_assoc, hdF D hD, LinearMap.zero_comp]

end CFSG.LieType.AlgebraicGroups
