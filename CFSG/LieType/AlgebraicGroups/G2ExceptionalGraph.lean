module

public import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
public import CFSG.LieType.Chevalley.LangG2ClosureExceptional
public import CFSG.LieType.Chevalley.LangG2Tangent
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv TensorProduct

open scoped CFSG.ConvolutionPoints

@[expose] def g2LabelEquiv
    : Label Tag.G2 ≃ Fin 14 :=
  (Equiv.ofBijective g2FixedBasis g2FixedBasis_bijective).symm

section Graph

variable {L : Type} [Field L]

variable (L) in
@[expose] def IsG2Exceptional
    (Φ : MulAut (adjointGroup Tag.G2 L)) : Prop :=
  ∀ c : L, Φ (xElement ⟨0, by decide⟩ c) = xElement ⟨1, by decide⟩ c ∧
    Φ (yElement ⟨0, by decide⟩ c) = yElement ⟨1, by decide⟩ c ∧
    Φ (xElement ⟨1, by decide⟩ c) = xElement ⟨0, by decide⟩ (c ^ 3) ∧
    Φ (yElement ⟨1, by decide⟩ c) = yElement ⟨0, by decide⟩ (c ^ 3)

@[expose] def g2GraphHom
    (Φ : MulAut (adjointGroup Tag.G2 L)) :
    adjointGroup Tag.G2 L →* Matrix.GeneralLinearGroup (Fin 14) L :=
  (glReindex g2LabelEquiv).toMonoidHom.comp
    ((modGLEquivGL Tag.G2 L).toMonoidHom.comp ((adjointGroup Tag.G2 L).subtype.comp Φ.toMonoidHom))

theorem g2GraphHom_apply
    (Φ : MulAut (adjointGroup Tag.G2 L)) (g : adjointGroup Tag.G2 L) :
    g2GraphHom Φ g =
      glReindex g2LabelEquiv (modGLEquivGL Tag.G2 L ((Φ g : adjointGroup Tag.G2 L) :
        ModGL Tag.G2 L)) :=
  rfl

@[expose] def g2LetterCurveCo
    (l : Letter Tag.G2) (n : ℕ) :
    GLCoord L (Fin 14) →ₐ[L] Polynomial L :=
  (unitCo L (letterUnit Tag.G2 (Polynomial L) l (Polynomial.X ^ n))).comp
    (glReindexCo g2LabelEquiv)

theorem toConv_aeval_comp_g2LetterCurveCo
    (l : Letter Tag.G2) (n : ℕ) (c : L) :
    toConv ((Polynomial.aeval c).comp (g2LetterCurveCo l n)) =
      glPointEquiv (glReindex g2LabelEquiv
        (modGLEquivGL Tag.G2 L (letterUnit Tag.G2 L l (c ^ n)))) := by
  have hb := baseChange_letterUnit ((Polynomial.aeval c : Polynomial L →ₐ[L] L) :
    Polynomial L →+* L) l (Polynomial.X ^ n)
  have h1 := comp_unitCo_of_baseChange (Polynomial.aeval c) _ _ hb
  rw [g2LetterCurveCo, ← AlgHom.comp_assoc, h1]
  apply glPointEquiv.symm.injective
  have hm : ∀ g : ModGL Tag.G2 L, modGLPoint Tag.G2 L g = glPointEquiv (modGLEquivGL Tag.G2 L g) :=
    fun _ => rfl
  rw [glPointEquiv_symm_comp_glReindexCo, toConv_ofConv, MulEquiv.symm_apply_apply, hm,
    MulEquiv.symm_apply_apply]
  congr 2
  simp

theorem g2GraphHom_regular_x
    {Φ : MulAut (adjointGroup Tag.G2 L)} (hΦ : IsG2Exceptional L Φ) :
    ∀ i, ∃ φ : GLCoord L (Fin 14) →ₐ[L] Polynomial L, ∀ c,
      toConv ((Polynomial.aeval c).comp φ) = glPointEquiv (g2GraphHom Φ (adjX Tag.G2 L i c)) := by
  intro i
  fin_cases i
  · refine ⟨g2LetterCurveCo (⟨1, by decide⟩, true) 1, fun c => ?_⟩
    rw [toConv_aeval_comp_g2LetterCurveCo, g2GraphHom_apply, pow_one]
    change _ = glPointEquiv (glReindex g2LabelEquiv (modGLEquivGL Tag.G2 L
      ((Φ (xElement ⟨0, by decide⟩ c) : adjointGroup Tag.G2 L) : ModGL Tag.G2 L)))
    rw [(hΦ c).1]
    rfl
  · refine ⟨g2LetterCurveCo (⟨0, by decide⟩, true) 3, fun c => ?_⟩
    rw [toConv_aeval_comp_g2LetterCurveCo, g2GraphHom_apply]
    change _ = glPointEquiv (glReindex g2LabelEquiv (modGLEquivGL Tag.G2 L
      ((Φ (xElement ⟨1, by decide⟩ c) : adjointGroup Tag.G2 L) : ModGL Tag.G2 L)))
    rw [(hΦ c).2.2.1]
    rfl

theorem g2GraphHom_regular_y
    {Φ : MulAut (adjointGroup Tag.G2 L)} (hΦ : IsG2Exceptional L Φ) :
    ∀ i, ∃ φ : GLCoord L (Fin 14) →ₐ[L] Polynomial L, ∀ c,
      toConv ((Polynomial.aeval c).comp φ) = glPointEquiv (g2GraphHom Φ (adjY Tag.G2 L i c)) := by
  intro i
  fin_cases i
  · refine ⟨g2LetterCurveCo (⟨1, by decide⟩, false) 1, fun c => ?_⟩
    rw [toConv_aeval_comp_g2LetterCurveCo, g2GraphHom_apply, pow_one]
    change _ = glPointEquiv (glReindex g2LabelEquiv (modGLEquivGL Tag.G2 L
      ((Φ (yElement ⟨0, by decide⟩ c) : adjointGroup Tag.G2 L) : ModGL Tag.G2 L)))
    rw [(hΦ c).2.1]
    rfl
  · refine ⟨g2LetterCurveCo (⟨0, by decide⟩, false) 3, fun c => ?_⟩
    rw [toConv_aeval_comp_g2LetterCurveCo, g2GraphHom_apply]
    change _ = glPointEquiv (glReindex g2LabelEquiv (modGLEquivGL Tag.G2 L
      ((Φ (yElement ⟨1, by decide⟩ c) : adjointGroup Tag.G2 L) : ModGL Tag.G2 L)))
    rw [(hΦ c).2.2.2]
    rfl

end Graph

section GraphEquiv

variable {τ : Tag} {k : Type} [Field k] {M : ℕ}

@[expose] def graphSubgroupEquiv
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k) :
    adjointGroup τ k ≃* graphSubgroup ψ :=
  MonoidHom.ofInjective (f := (adjointGroup τ k).subtype.prod ψ)
    fun _ _ h => Subtype.ext (congrArg Prod.fst h)

theorem coe_graphSubgroupEquiv_symm
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k) (γ : graphSubgroup ψ) :
    ((graphSubgroupEquiv ψ).symm γ : ModGL τ k) =
      (γ : ModGL τ k × Matrix.GeneralLinearGroup (Fin M) k).1 := by
  conv_rhs => rw [← (graphSubgroupEquiv ψ).apply_symm_apply γ]
  rfl

end GraphEquiv

section QuotientPoints

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A] {G : Type} [Group G]

@[expose] def mapQuotientPointsEquiv (E : G ≃* WithConv (A →ₐ[k] k)) (H : Subgroup G)
    (h : pointsZero k (subgroupIdeal (H.map E.toMonoidHom)) =
      subgroupPoints (H.map E.toMonoidHom)) :
    WithConv ((A ⧸ subgroupIdeal (H.map E.toMonoidHom)) →ₐ[k] k) ≃* H :=
  (subgroupQuotientPointsEquiv _ h).trans (E.subgroupMap H).symm

theorem coe_mapQuotientPointsEquiv (E : G ≃* WithConv (A →ₐ[k] k)) (H : Subgroup G)
    (h : pointsZero k (subgroupIdeal (H.map E.toMonoidHom)) =
      subgroupPoints (H.map E.toMonoidHom))
    (φ : WithConv ((A ⧸ subgroupIdeal (H.map E.toMonoidHom)) →ₐ[k] k)) :
    ((mapQuotientPointsEquiv E H h φ : H) : G) =
      E.symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) :=
  rfl

end QuotientPoints

section Projection

variable {L : Type} [Field L]

theorem tmul_one_mem_subgroupIdeal_graph
    (Φ : MulAut (adjointGroup Tag.G2 L))
    {a : GLCoord L (Label Tag.G2)} (ha : a ∈ subgroupIdeal (adjointPointSubgroup Tag.G2 L)) :
    a ⊗ₜ (1 : GLCoord L (Fin 14)) ∈ subgroupIdeal (graphPointSubgroup (g2GraphHom Φ)) := by
  refine mem_pointsIdeal.2 fun y hy => ?_
  rw [subgroupPoints_map, transportPoints_graphSubgroup] at hy
  obtain ⟨g, rfl⟩ := hy
  rw [tensorPointEquiv_tmul, map_one, mul_one]
  refine mem_pointsIdeal.1 ha _ ((mem_subgroupPoints_adjointPointSubgroup Tag.G2 L).2 ?_)
  rw [toConv_ofConv, MulEquiv.symm_apply_apply]
  exact g.2

variable [IsAlgClosed L]

variable (L) in
abbrev g2GraphCoord
    (Φ : MulAut (adjointGroup Tag.G2 L)) : Type :=
  GLCoord L (Label Tag.G2) ⊗[L] GLCoord L (Fin 14) ⧸
    subgroupIdeal (graphPointSubgroup (g2GraphHom Φ))

theorem g2Graph_realization
    {Φ : MulAut (adjointGroup Tag.G2 L)} (hΦ : IsG2Exceptional L Φ) :
    IsPointClosed L (graphPoints Tag.G2 L (g2GraphHom Φ)) ∧
      IsConnectedAlgebraicSubgroup L (graphPointSubgroup (g2GraphHom Φ)) ∧
      Algebra.Smooth L (g2GraphCoord L Φ) ∧ IrreducibleSpace (PrimeSpectrum (g2GraphCoord L Φ)) :=
  let h := (exceptional_Lang_exact_affine_group_realization L Tag.G2).2 14 (g2GraphHom Φ)
    (g2GraphHom_regular_x hΦ) (g2GraphHom_regular_y hΦ)
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

@[expose] def g2GraphPointEquiv
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) : WithConv (g2GraphCoord L Φ →ₐ[L] L) ≃* adjointGroup Tag.G2 L :=
  (mapQuotientPointsEquiv (modGLPairPoint Tag.G2 L 14) (graphSubgroup (g2GraphHom Φ))
    (g2Graph_realization hΦ).2.1.pointsZero_eq).trans (graphSubgroupEquiv _).symm

theorem coe_g2GraphPointEquiv
    {Φ : MulAut (adjointGroup Tag.G2 L)} (hΦ : IsG2Exceptional L Φ)
    (z : WithConv (g2GraphCoord L Φ →ₐ[L] L)) :
    (g2GraphPointEquiv hΦ z : ModGL Tag.G2 L) = (modGLPoint Tag.G2 L).symm
      (toConv ((z.ofConv.comp (Ideal.Quotient.mkₐ L _)).comp
        Algebra.TensorProduct.includeLeft)) := by
  rw [g2GraphPointEquiv, MulEquiv.trans_apply, coe_graphSubgroupEquiv_symm,
    coe_mapQuotientPointsEquiv]
  rfl

@[expose] def g2GraphProjCo
    (Φ : MulAut (adjointGroup Tag.G2 L)) :
    realizedCoord Tag.G2 L →ₐc[L] g2GraphCoord L Φ :=
  bialgHomQuotientLift (subgroupIdeal (adjointPointSubgroup Tag.G2 L))
    ((Bialgebra.Quotient.mkBialgHom (subgroupIdeal (graphPointSubgroup (g2GraphHom Φ)))).comp
      (includeLeftBialgHom L (GLCoord L (Label Tag.G2)) (GLCoord L (Fin 14))))
    (fun a ha => by
      rw [BialgHom.comp_apply, includeLeftBialgHom_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (tmul_one_mem_subgroupIdeal_graph Φ ha))

theorem g2GraphProjCo_mk
    (Φ : MulAut (adjointGroup Tag.G2 L)) (a : GLCoord L (Label Tag.G2)) :
    g2GraphProjCo Φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (a ⊗ₜ 1) := by
  rw [g2GraphProjCo, bialgHomQuotientLift_mk, BialgHom.comp_apply, includeLeftBialgHom_apply]
  rfl

theorem g2GraphProjCo_comp_mkₐ
    (Φ : MulAut (adjointGroup Tag.G2 L)) :
    (g2GraphProjCo Φ : realizedCoord Tag.G2 L →ₐ[L] g2GraphCoord L Φ).comp
        (Ideal.Quotient.mkₐ L _) =
      (Ideal.Quotient.mkₐ L _).comp Algebra.TensorProduct.includeLeft :=
  AlgHom.ext fun a => g2GraphProjCo_mk Φ a

theorem realizedPointEquiv_comp_g2GraphProjCo
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) (z : WithConv (g2GraphCoord L Φ →ₐ[L] L)) :
    realizedPointEquiv Tag.G2 L
        (toConv (z.ofConv.comp (g2GraphProjCo Φ : realizedCoord Tag.G2 L →ₐ[L] _))) =
      g2GraphPointEquiv hΦ z := by
  apply Subtype.ext
  rw [coe_realizedPointEquiv, coe_g2GraphPointEquiv, ofConv_toConv, AlgHom.comp_assoc,
    g2GraphProjCo_comp_mkₐ, AlgHom.comp_assoc]

theorem bijective_g2GraphProjCo_points
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) :
    Function.Bijective fun z : WithConv (g2GraphCoord L Φ →ₐ[L] L) =>
      toConv (z.ofConv.comp (g2GraphProjCo Φ : realizedCoord Tag.G2 L →ₐ[L] _)) := by
  have h : (fun z : WithConv (g2GraphCoord L Φ →ₐ[L] L) =>
      toConv (z.ofConv.comp (g2GraphProjCo Φ : realizedCoord Tag.G2 L →ₐ[L] _))) =
      (realizedPointEquiv Tag.G2 L).symm ∘ g2GraphPointEquiv hΦ := by
    funext z
    rw [Function.comp_apply, ← realizedPointEquiv_comp_g2GraphProjCo hΦ,
      MulEquiv.symm_apply_apply]
  rw [h]
  exact (realizedPointEquiv Tag.G2 L).symm.bijective.comp (g2GraphPointEquiv hΦ).bijective

end Projection

end CFSG.LieType.AlgebraicGroups
