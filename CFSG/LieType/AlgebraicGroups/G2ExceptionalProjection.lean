module

public import CFSG.LieType.AlgebraicGroups.G2ExceptionalBound
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalCurves
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv TensorProduct Module

open scoped CFSG.ConvolutionPoints

theorem bijective_of_linearIndependent_comp {K V W : Type} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    {n : ℕ} (hV : finrank K V ≤ n) (hW : finrank K W ≤ n) (f : V →ₗ[K] W) {ι : Type} [Fintype ι]
    (hι : Fintype.card ι = n) {v : ι → V} (hv : LinearIndependent K (f ∘ v)) :
    Function.Bijective f ∧ finrank K V = n ∧ finrank K W = n := by
  have hW' : finrank K W = n := le_antisymm hW (hι ▸ hv.fintype_card_le_finrank)
  have hV' : finrank K V = n := le_antisymm hV (hι ▸ (hv.of_comp f).fintype_card_le_finrank)
  have hspan := hv.span_eq_top_of_card_eq_finrank' (hι.trans hW'.symm)
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, rfl⟩
  exact ⟨⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hV'.trans hW'.symm)).2
    hsurj, hsurj⟩, hV', hW'⟩

section Entries

variable {τ : Tag} {L : Type} [Field L]

@[expose] def tangentEntries
    (x : realizedCoord τ L →ₐ[L] L) :
    TangentSpace L (realizedCoord τ L) x →ₗ[L] Matrix (Label τ) (Label τ) L where
  toFun D := Matrix.of fun a b =>
    (D : realizedCoord τ L →ₗ[L] L) (Ideal.Quotient.mk _ (glEntry L (Label τ) a b))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tangentEntries_apply
    (x : realizedCoord τ L →ₐ[L] L)
    (D : TangentSpace L (realizedCoord τ L) x) (a b : Label τ) :
    tangentEntries x D a b =
      (D : realizedCoord τ L →ₗ[L] L) (Ideal.Quotient.mk _ (glEntry L (Label τ) a b)) :=
  rfl

end Entries

section G2

variable {L : Type} [Field L] [IsAlgClosed L]

theorem modGLPairPoint_symm_g2Graph
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) (z : WithConv (g2GraphCoord L Φ →ₐ[L] L)) :
    (modGLPairPoint Tag.G2 L 14).symm (toConv (z.ofConv.comp (Ideal.Quotient.mkₐ L _))) =
      ((g2GraphPointEquiv hΦ z : ModGL Tag.G2 L), g2GraphHom Φ (g2GraphPointEquiv hΦ z)) := by
  rw [← coe_mapQuotientPointsEquiv (modGLPairPoint Tag.G2 L 14) (graphSubgroup (g2GraphHom Φ))
    (g2Graph_realization hΦ).2.1.pointsZero_eq z]
  conv_lhs => rw [← (graphSubgroupEquiv (g2GraphHom Φ)).apply_symm_apply
    (mapQuotientPointsEquiv _ _ (g2Graph_realization hΦ).2.1.pointsZero_eq z)]
  rfl

theorem exists_linearIndependent_g2GraphProj
    [CharP L 3] {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) :
    ∃ v : {α // IsRoot Tag.G2 α} ⊕ Fin Tag.G2.rank →
        TangentSpace L (g2GraphCoord L Φ) (Bialgebra.counitAlgHom L _),
      LinearIndependent L (tangentMap (g2GraphProjCo Φ : realizedCoord Tag.G2 L →ₐ[L] _)
        (BialgHom.counitAlgHom_comp (g2GraphProjCo Φ)) ∘ v) := by
  choose φx hφx using g2GraphHom_regular_x hΦ
  choose φy hφy using g2GraphHom_regular_y hΦ
  let v : {α // IsRoot Tag.G2 α} ⊕ Fin Tag.G2.rank →
      TangentSpace L (g2GraphCoord L Φ) (Bialgebra.counitAlgHom L _) :=
    Sum.elim (fun α => ⟨_, pinnedCurve_mem φx φy (g2GraphHom Φ) hφx hφy α.1⟩)
      (fun i => ⟨_, torusCurve_mem φx φy (g2GraphHom Φ) hφx hφy i⟩)
  refine ⟨v, LinearIndependent.of_comp (tangentEntries _) ?_⟩
  have hli := (linearIndependent_pinnedE_tangentH L).map'
    (LinearMap.toMatrixAlgEquiv (Finsupp.basisSingleOne (R := L)
      (ι := Label Tag.G2))).toLinearEquiv.toLinearMap (LinearEquiv.ker _)
  convert hli using 1
  funext x
  ext a b
  rcases x with α | i
  · show dualTangent ((Polynomial.aeval (DualNumber.eps : DualNumber L)).comp
        (graphCurveCo φx φy (g2GraphHom Φ) hφx hφy
          (pinnedWord Tag.G2 (Polynomial L) α.1 Polynomial.X)))
        (g2GraphProjCo Φ (Ideal.Quotient.mk _ (glEntry L (Label Tag.G2) a b))) =
      endMatrix Tag.G2 (pinnedE Tag.G2 L α.1) a b
    rw [g2GraphProjCo_mk, pinnedCurve_mk, endMatrix_apply]
  · show dualTangent ((torusDualPoint L).comp (graphCurveCo φx φy (g2GraphHom Φ) hφx hφy
        (torusWord Tag.G2 (TorusAffine L 1 0) i (torusUnit L 1 0 0))))
        (g2GraphProjCo Φ (Ideal.Quotient.mk _ (glEntry L (Label Tag.G2) a b))) =
      endMatrix Tag.G2 (tangentH Tag.G2 L i) a b
    rw [g2GraphProjCo_mk, torusCurve_mk, endMatrix_apply]

end G2

theorem exceptional_Lang_G2_exceptional_graph_tangent_projection
    (L : Type) [Field L]
    [IsAlgClosed L] [CharP L 3] (Φ : MulAut (adjointGroup Tag.G2 L)) (hΦ : IsG2Exceptional L Φ) :
    (IsPointClosed L (groupPoints Tag.G2 L) ∧
      IsConnectedAlgebraicSubgroup L (adjointPointSubgroup Tag.G2 L) ∧
      Algebra.Smooth L (realizedCoord Tag.G2 L) ∧
      IrreducibleSpace (PrimeSpectrum (realizedCoord Tag.G2 L))) ∧
    (IsPointClosed L (graphPoints Tag.G2 L (g2GraphHom Φ)) ∧
      IsConnectedAlgebraicSubgroup L (graphPointSubgroup (g2GraphHom Φ)) ∧
      Algebra.Smooth L (g2GraphCoord L Φ) ∧ IrreducibleSpace (PrimeSpectrum (g2GraphCoord L Φ)) ∧
      ∀ z : WithConv (g2GraphCoord L Φ →ₐ[L] L),
        (modGLPairPoint Tag.G2 L 14).symm (toConv (z.ofConv.comp (Ideal.Quotient.mkₐ L _))) =
          ((g2GraphPointEquiv hΦ z : ModGL Tag.G2 L), g2GraphHom Φ (g2GraphPointEquiv hΦ z))) ∧
    (∀ z : WithConv (g2GraphCoord L Φ →ₐ[L] L),
      realizedPointEquiv Tag.G2 L
          (toConv (z.ofConv.comp (g2GraphProjCo Φ : realizedCoord Tag.G2 L →ₐ[L] _))) =
        g2GraphPointEquiv hΦ z) ∧
    Function.Bijective (fun z : WithConv (g2GraphCoord L Φ →ₐ[L] L) =>
      toConv (z.ofConv.comp (g2GraphProjCo Φ : realizedCoord Tag.G2 L →ₐ[L] _))) ∧
    Function.Bijective (tangentMap
      (g2GraphProjCo Φ : realizedCoord Tag.G2 L →ₐ[L] g2GraphCoord L Φ)
      (BialgHom.counitAlgHom_comp (g2GraphProjCo Φ))) ∧
    finrank L (TangentSpace L (realizedCoord Tag.G2 L) (Bialgebra.counitAlgHom L _)) = 14 ∧
    finrank L (TangentSpace L (g2GraphCoord L Φ) (Bialgebra.counitAlgHom L _)) = 14 := by
  have hG := (exceptional_Lang_exact_affine_group_realization L Tag.G2).1
  have hΓ := g2Graph_realization hΦ
  have := hG.2.1.finiteType
  have := hΓ.2.1.finiteType
  have : FiniteDimensional L
      (TangentSpace L (realizedCoord Tag.G2 L) (Bialgebra.counitAlgHom L _)) :=
    finiteDimensional_tangentSpace _
  have : FiniteDimensional L
      (TangentSpace L (g2GraphCoord L Φ) (Bialgebra.counitAlgHom L _)) :=
    finiteDimensional_tangentSpace _
  have hcard : Fintype.card ({α // IsRoot Tag.G2 α} ⊕ Fin Tag.G2.rank) = 14 := by
    rw [Fintype.card_sum, Fintype.card_fin,
      Fintype.card_of_subtype (rootFinset Tag.G2) fun _ => mem_rootFinset]
    decide
  obtain ⟨v, hv⟩ := exists_linearIndependent_g2GraphProj hΦ
  obtain ⟨hbij, hΓ14, hG14⟩ := bijective_of_linearIndependent_comp
    (finrank_tangentSpace_g2GraphCoord_le hΦ _) (finrank_tangentSpace_realizedCoord_G2_le _) _
    hcard hv
  exact ⟨⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1⟩,
    ⟨hΓ.1, hΓ.2.1, hΓ.2.2.1, hΓ.2.2.2, modGLPairPoint_symm_g2Graph hΦ⟩,
    realizedPointEquiv_comp_g2GraphProjCo hΦ, bijective_g2GraphProjCo_points hΦ, hbij, hG14,
    hΓ14⟩

end CFSG.LieType.AlgebraicGroups
