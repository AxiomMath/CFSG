module

public import CFSG.LieType.AlgebraicGroups.G2ExceptionalGraph
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv
  TensorProduct

open scoped CFSG.ConvolutionPoints

section Dual

variable {τ : Tag}

theorem baseChange_tangentH {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (i : Fin τ.rank) : BaseChange f (tangentH τ R i) (tangentH τ S i) := by
  intro b
  rcases b with j | α
  · simp [tangentH]
  · simp [tangentH, Finsupp.mapRange_single]

variable {k : Type} [Field k]

theorem snd_single_one (a b : Label τ) :
    ((Finsupp.single b (1 : DualNumber k) : RootModule τ (DualNumber k)) a).snd = 0 := by
  rw [Finsupp.single_apply]
  split_ifs <;> simp

theorem snd_one_add_eps_smul_apply (E : Module.End (DualNumber k) (RootModule τ (DualNumber k)))
    (a b : Label τ) :
    ((((1 : Module.End (DualNumber k) (RootModule τ (DualNumber k))) +
        (DualNumber.eps : DualNumber k) • E) (Finsupp.single b 1)) a).snd =
      (E (Finsupp.single b 1) a).fst := by
  rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, TrivSqZeroExt.snd_add, snd_single_one, DualNumber.snd_mul,
    DualNumber.fst_eps, DualNumber.snd_eps]
  ring

theorem fst_apply_of_baseChange {E : Module.End (DualNumber k) (RootModule τ (DualNumber k))}
    {E' : Module.End k (RootModule τ k)}
    (h : BaseChange (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k) E E') (a b : Label τ) :
    (E (Finsupp.single b 1) a).fst = E' (Finsupp.single b 1) a := by
  rw [← h b, Finsupp.mapRange_apply]
  rfl

theorem tensorPointEquiv_one {A B : Type} [CommRing A] [HopfAlgebra k A] [CommRing B]
    [HopfAlgebra k B] :
    tensorPointEquiv ((1 : WithConv (A →ₐ[k] k)).ofConv, (1 : WithConv (B →ₐ[k] k)).ofConv) =
      (1 : WithConv (A ⊗[k] B →ₐ[k] k)).ofConv := by
  rw [← tensorPointMulEquiv_symm_apply]
  exact congrArg ofConv
    (map_one (tensorPointMulEquiv : WithConv (A ⊗[k] B →ₐ[k] k) ≃* _).symm)

variable (k) in
@[expose] def torusDualPoint : TorusAffine k 1 0 →ₐ[k] DualNumber k :=
  IsLocalization.Away.liftAlgHom (torusAffineDet k 1 0)
    (f := MvPolynomial.aeval (Sum.elim (fun _ => ((dualOneAddEps k : (DualNumber k)ˣ) :
      DualNumber k)) Fin.elim0)) (by
      rw [torusAffineDet, map_prod]
      exact IsUnit.prod_univ_iff.2 fun _ => by
        rw [MvPolynomial.aeval_X, Sum.elim_inl]
        exact (dualOneAddEps k).isUnit)

theorem torusDualPoint_torusCoord :
    torusDualPoint k (torusCoord k 1 0 0) = 1 + DualNumber.eps := by
  rw [torusDualPoint, IsLocalization.Away.liftAlgHom_apply, torusCoord,
    IsLocalization.Away.lift_eq]
  simp [dualOneAddEps]

end Dual

section GraphWord

variable {τ : Tag} {k : Type} [Field k] {M : ℕ}
  (φx φy : Fin τ.rank → (GLCoord k (Fin M) →ₐ[k] Polynomial k)) {D : Type} [CommRing D]
  [Algebra k D]

@[expose] def graphWordCo
    (w : List (Letter τ × D)) :
    GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) →ₐ[k] D :=
  Algebra.TensorProduct.productMap (unitCo k (wordUnit τ D w)) (psiWordCo φx φy w).ofConv

theorem graphWordCo_tmul_one
    (w : List (Letter τ × D)) (a b : Label τ) :
    graphWordCo φx φy w (glEntry k (Label τ) a b ⊗ₜ 1) =
      (wordUnit τ D w : Module.End D (RootModule τ D)) (Finsupp.single b 1) a := by
  rw [graphWordCo, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, unitCo,
    GLCoord.lift_glEntry, endMatrix_apply]

theorem comp_graphWordCo
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k)
    (hx : ∀ i c, toConv ((Polynomial.aeval c).comp (φx i)) = glPointEquiv (ψ (adjX τ k i c)))
    (hy : ∀ i c, toConv ((Polynomial.aeval c).comp (φy i)) = glPointEquiv (ψ (adjY τ k i c)))
    (z : D →ₐ[k] k) (w : List (Letter τ × D)) :
    z.comp (graphWordCo φx φy w) = tensorPointEquiv
      ((modGLPoint τ k (wordElt τ (mapWord (z : D →+* k) w))).ofConv,
        (glPointEquiv (ψ (wordElt τ (mapWord (z : D →+* k) w)))).ofConv) := by
  rw [graphWordCo, comp_productMap, comp_unitCo_wordUnit, coe_wordElt,
    ← point_psiWordCo ψ φx φy hx hy z w, ofConv_toConv]

theorem comp_graphWordCo_mem
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k)
    (hx : ∀ i c, toConv ((Polynomial.aeval c).comp (φx i)) = glPointEquiv (ψ (adjX τ k i c)))
    (hy : ∀ i c, toConv ((Polynomial.aeval c).comp (φy i)) = glPointEquiv (ψ (adjY τ k i c)))
    (z : D →ₐ[k] k) (w : List (Letter τ × D)) :
    z.comp (graphWordCo φx φy w) ∈ subgroupPoints (graphPointSubgroup ψ) := by
  rw [subgroupPoints_map, transportPoints_graphSubgroup, comp_graphWordCo φx φy ψ hx hy]
  exact ⟨_, rfl⟩

variable [IsAlgClosed k] [Algebra.FiniteType k D] [IsReduced D]

@[expose] def graphCurveCo
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k)
    (hx : ∀ i c, toConv ((Polynomial.aeval c).comp (φx i)) = glPointEquiv (ψ (adjX τ k i c)))
    (hy : ∀ i c, toConv ((Polynomial.aeval c).comp (φy i)) = glPointEquiv (ψ (adjY τ k i c)))
    (w : List (Letter τ × D)) :
    (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸ subgroupIdeal (graphPointSubgroup ψ)) →ₐ[k] D :=
  liftOfPoints _ (graphWordCo φx φy w) fun z => comp_graphWordCo_mem φx φy ψ hx hy z w

variable
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k)
  (hx : ∀ i c, toConv ((Polynomial.aeval c).comp (φx i)) = glPointEquiv (ψ (adjX τ k i c)))
  (hy : ∀ i c, toConv ((Polynomial.aeval c).comp (φy i)) = glPointEquiv (ψ (adjY τ k i c)))

theorem comp_graphCurveCo_eq_counit
    {w : List (Letter τ × D)} {z : D →ₐ[k] k}
    (h1 : wordElt τ (mapWord (z : D →+* k) w) = 1) :
    z.comp (graphCurveCo φx φy ψ hx hy w) = Bialgebra.counitAlgHom k
      (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸ subgroupIdeal (graphPointSubgroup ψ)) := by
  refine Ideal.Quotient.algHom_ext k ?_
  rw [AlgHom.comp_assoc, graphCurveCo, liftOfPoints_comp_mkₐ, comp_graphWordCo φx φy ψ hx hy, h1,
    OneMemClass.coe_one, map_one, map_one, map_one, tensorPointEquiv_one,
    convOne_ofConv_eq_counit]
  exact AlgHom.ext fun _ => rfl

theorem dualTangent_graphCurveCo_mem
    {w : List (Letter τ × D)} (e : D →ₐ[k] DualNumber k)
    (h1 : wordElt τ (mapWord (((TrivSqZeroExt.fstHom k k k).comp e : D →ₐ[k] k) : D →+* k) w) =
      1) :
    dualTangent (e.comp (graphCurveCo φx φy ψ hx hy w)) ∈ tangentSpace k _
      (Bialgebra.counitAlgHom k
        (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸ subgroupIdeal (graphPointSubgroup ψ))) := by
  have h := dualTangent_mem (e.comp (graphCurveCo φx φy ψ hx hy w))
  rwa [← AlgHom.comp_assoc, comp_graphCurveCo_eq_counit φx φy ψ hx hy h1] at h

theorem dualTangent_graphCurveCo_mk
    (w : List (Letter τ × D)) (e : D →ₐ[k] DualNumber k)
    (a b : Label τ) :
    dualTangent (e.comp (graphCurveCo φx φy ψ hx hy w))
        (Ideal.Quotient.mk _ (glEntry k (Label τ) a b ⊗ₜ 1)) =
      ((wordUnit τ (DualNumber k) (mapWord (e : D →+* DualNumber k) w) :
        Module.End (DualNumber k) (RootModule τ (DualNumber k))) (Finsupp.single b 1) a).snd := by
  rw [dualTangent_apply, AlgHom.comp_apply, graphCurveCo, liftOfPoints_mk, graphWordCo_tmul_one,
    ← baseChange_wordUnit (e : D →+* DualNumber k) w b, Finsupp.mapRange_apply]
  rfl

end GraphWord

section Curves

variable
    {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] {M : ℕ}
  (φx φy : Fin τ.rank → (GLCoord k (Fin M) →ₐ[k] Polynomial k))
  (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k)
  (hx : ∀ i c, toConv ((Polynomial.aeval c).comp (φx i)) = glPointEquiv (ψ (adjX τ k i c)))
  (hy : ∀ i c, toConv ((Polynomial.aeval c).comp (φy i)) = glPointEquiv (ψ (adjY τ k i c)))

theorem pinnedCurve_mem
    (α : Fin τ.rank → ℤ) :
    dualTangent ((Polynomial.aeval (DualNumber.eps : DualNumber k)).comp
      (graphCurveCo φx φy ψ hx hy (pinnedWord τ (Polynomial k) α Polynomial.X))) ∈
      tangentSpace k _ (Bialgebra.counitAlgHom k
        (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸ subgroupIdeal (graphPointSubgroup ψ))) := by
  refine dualTangent_graphCurveCo_mem φx φy ψ hx hy _ (Subtype.ext ?_)
  have h0 : (((TrivSqZeroExt.fstHom k k k).comp (Polynomial.aeval DualNumber.eps) :
      Polynomial k →ₐ[k] k) : Polynomial k →+* k) Polynomial.X = 0 := by
    simp
  rw [mapWord_pinnedWord, coe_wordElt, wordUnit_pinnedWord, OneMemClass.coe_one, h0, pinnedX_zero]

theorem torusCurve_mem
    (i : Fin τ.rank) :
    dualTangent ((torusDualPoint k).comp (graphCurveCo φx φy ψ hx hy
      (torusWord τ (TorusAffine k 1 0) i (torusUnit k 1 0 0)))) ∈
      tangentSpace k _ (Bialgebra.counitAlgHom k
        (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸ subgroupIdeal (graphPointSubgroup ψ))) := by
  refine dualTangent_graphCurveCo_mem φx φy ψ hx hy _ (Subtype.ext ?_)
  have h1 : Units.map (((TrivSqZeroExt.fstHom k k k).comp (torusDualPoint k) :
      TorusAffine k 1 0 →ₐ[k] k) : TorusAffine k 1 0 →+* k).toMonoidHom
        (torusUnit k 1 0 0) = 1 := by
    ext
    simp [coe_torusUnit, torusDualPoint_torusCoord]
  rw [mapWord_torusWord, coe_wordElt, wordUnit_torusWord, OneMemClass.coe_one, h1, torusElt_one]

theorem pinnedCurve_mk
    (α : Fin τ.rank → ℤ) (a b : Label τ) :
    dualTangent ((Polynomial.aeval (DualNumber.eps : DualNumber k)).comp
      (graphCurveCo φx φy ψ hx hy (pinnedWord τ (Polynomial k) α Polynomial.X)))
        (Ideal.Quotient.mk _ (glEntry k (Label τ) a b ⊗ₜ 1)) =
      pinnedE τ k α (Finsupp.single b 1) a := by
  have hε : ((Polynomial.aeval (DualNumber.eps : DualNumber k) :
      Polynomial k →ₐ[k] DualNumber k) : Polynomial k →+* DualNumber k) Polynomial.X =
        DualNumber.eps :=
    Polynomial.aeval_X _
  rw [dualTangent_graphCurveCo_mk, mapWord_pinnedWord, wordUnit_pinnedWord, hε,
    pinnedX_of_mul_self_eq_zero α DualNumber.eps_mul_eps, snd_one_add_eps_smul_apply,
    fst_apply_of_baseChange (baseChange_pinnedE _ α)]

theorem torusCurve_mk
    (i : Fin τ.rank) (a b : Label τ) :
    dualTangent ((torusDualPoint k).comp (graphCurveCo φx φy ψ hx hy
      (torusWord τ (TorusAffine k 1 0) i (torusUnit k 1 0 0))))
        (Ideal.Quotient.mk _ (glEntry k (Label τ) a b ⊗ₜ 1)) =
      tangentH τ k i (Finsupp.single b 1) a := by
  have hu : ((Units.map ((torusDualPoint k : TorusAffine k 1 0 →ₐ[k] DualNumber k) :
      TorusAffine k 1 0 →+* DualNumber k).toMonoidHom (torusUnit k 1 0 0) : (DualNumber k)ˣ) :
        DualNumber k) = 1 + DualNumber.eps := by
    simp [coe_torusUnit, torusDualPoint_torusCoord]
  rw [dualTangent_graphCurveCo_mk, mapWord_torusWord, wordUnit_torusWord,
    torusElt_of_eq_one_add i hu DualNumber.eps_mul_eps, snd_one_add_eps_smul_apply,
    fst_apply_of_baseChange (baseChange_tangentH _ i)]

end Curves

end CFSG.LieType.AlgebraicGroups
