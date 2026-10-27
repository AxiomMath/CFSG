module

public import CFSG.LieType.AlgebraicGroups.G2ExceptionalProjection
public import CFSG.LieType.AlgebraicGroups.AdjointTangentAction
import CFSG.LieType.AlgebraicGroups.InnerInvolutionTorus
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} (L : Type) [Field L] [IsAlgClosed L]

omit
  [IsAlgClosed L] in
theorem comp_unitCo_wordUnit_mem {D : Type} [CommRing D] [Algebra L D] (z : D →ₐ[L] L)
    (w : List (Letter τ × D)) :
    z.comp (unitCo L (wordUnit τ D w)) ∈ subgroupPoints (adjointPointSubgroup τ L) := by
  rw [subgroupPoints_map, comp_unitCo_wordUnit, ← coe_wordElt]
  exact ⟨_, (wordElt τ (mapWord (z : D →+* L) w)).2, rfl⟩

@[expose] def realizedWordCo {D : Type} [CommRing D] [Algebra L D] [Algebra.FiniteType L D]
    [IsReduced D] (w : List (Letter τ × D)) : realizedCoord τ L →ₐ[L] D :=
  liftOfPoints _ (unitCo L (wordUnit τ D w)) fun z => comp_unitCo_wordUnit_mem L z w

private theorem comp_realizedWordCo_eq_counit {D : Type} [CommRing D] [Algebra L D]
    [Algebra.FiniteType L D] [IsReduced D] {w : List (Letter τ × D)} {z : D →ₐ[L] L}
    (h1 : wordElt τ (mapWord (z : D →+* L) w) = 1) :
    z.comp (realizedWordCo L w) =
      Bialgebra.counitAlgHom L (realizedCoord τ L) := by
  refine Ideal.Quotient.algHom_ext L ?_
  rw [AlgHom.comp_assoc, realizedWordCo, liftOfPoints_comp_mkₐ, comp_unitCo_wordUnit,
    ← coe_wordElt, h1, OneMemClass.coe_one, map_one, convOne_ofConv_eq_counit]
  exact AlgHom.ext fun a => rfl
theorem rootTangent_mem (α : Fin τ.rank → ℤ) :
    dualTangent ((Polynomial.aeval (DualNumber.eps : DualNumber L)).comp
      (realizedWordCo L (pinnedWord τ (Polynomial L) α Polynomial.X))) ∈
      tangentSpace L (realizedCoord τ L) (Bialgebra.counitAlgHom L (realizedCoord τ L)) := by
  have h1 : wordElt τ (mapWord (((TrivSqZeroExt.fstHom L L L).comp
      (Polynomial.aeval (DualNumber.eps : DualNumber L)) : Polynomial L →ₐ[L] L) :
      Polynomial L →+* L) (pinnedWord τ (Polynomial L) α Polynomial.X)) = 1 := by
    refine Subtype.ext ?_
    have h0 : (((TrivSqZeroExt.fstHom L L L).comp (Polynomial.aeval DualNumber.eps) :
        Polynomial L →ₐ[L] L) : Polynomial L →+* L) Polynomial.X = 0 := by simp
    rw [mapWord_pinnedWord, coe_wordElt, wordUnit_pinnedWord, OneMemClass.coe_one, h0,
      pinnedX_zero]
  have h := dualTangent_mem ((Polynomial.aeval (DualNumber.eps : DualNumber L)).comp
    (realizedWordCo L (pinnedWord τ (Polynomial L) α Polynomial.X)))
  rwa [← AlgHom.comp_assoc, comp_realizedWordCo_eq_counit (L := L) (D := Polynomial L)
    (w := pinnedWord τ (Polynomial L) α Polynomial.X) (z :=
    (TrivSqZeroExt.fstHom L L L).comp (Polynomial.aeval (DualNumber.eps : DualNumber L))) h1] at h

theorem torusTangent_mem (i : Fin τ.rank) :
    dualTangent ((torusDualPoint L).comp
      (realizedWordCo L (torusWord τ (TorusAffine L 1 0) i (torusUnit L 1 0 0)))) ∈
      tangentSpace L (realizedCoord τ L) (Bialgebra.counitAlgHom L (realizedCoord τ L)) := by
  have h1 : wordElt τ (mapWord (((TrivSqZeroExt.fstHom L L L).comp (torusDualPoint L) :
      TorusAffine L 1 0 →ₐ[L] L) : TorusAffine L 1 0 →+* L)
      (torusWord τ (TorusAffine L 1 0) i (torusUnit L 1 0 0))) = 1 := by
    refine Subtype.ext ?_
    have hu : Units.map (((TrivSqZeroExt.fstHom L L L).comp (torusDualPoint L) :
        TorusAffine L 1 0 →ₐ[L] L) : TorusAffine L 1 0 →+* L).toMonoidHom
        (torusUnit L 1 0 0) = 1 := by
      ext
      simp [coe_torusUnit, torusDualPoint_torusCoord]
    rw [mapWord_torusWord, coe_wordElt, wordUnit_torusWord, OneMemClass.coe_one, hu,
      torusElt_one]
  have h := dualTangent_mem ((torusDualPoint L).comp (realizedWordCo L
    (torusWord τ (TorusAffine L 1 0) i (torusUnit L 1 0 0))))
  rwa [← AlgHom.comp_assoc, comp_realizedWordCo_eq_counit (L := L) (D := TorusAffine L 1 0)
    (w := torusWord τ (TorusAffine L 1 0) i (torusUnit L 1 0 0)) (z :=
    (TrivSqZeroExt.fstHom L L L).comp (torusDualPoint L)) h1] at h

private theorem dualTangent_realizedWordCo_mk {D : Type} [CommRing D] [Algebra L D]
    [Algebra.FiniteType L D] [IsReduced D] (w : List (Letter τ × D))
    (e : D →ₐ[L] DualNumber L) (a b : Label τ) :
    dualTangent (e.comp (realizedWordCo L w))
        (Ideal.Quotient.mk _ (glEntry L (Label τ) a b)) =
      ((wordUnit τ (DualNumber L) (mapWord (e : D →+* DualNumber L) w) :
        Module.End (DualNumber L) (RootModule τ (DualNumber L)))
        (Finsupp.single b 1) a).snd := by
  rw [dualTangent_apply, AlgHom.comp_apply, realizedWordCo, liftOfPoints_mk, unitCo,
    GLCoord.lift_glEntry, endMatrix_apply, ← baseChange_wordUnit (e : D →+* DualNumber L) w b,
    Finsupp.mapRange_apply]
  rfl

variable (τ) in
@[expose] def rootTangent (α : Fin τ.rank → ℤ) :
    TangentSpace L (realizedCoord τ L) (Bialgebra.counitAlgHom L (realizedCoord τ L)) :=
  ⟨_, rootTangent_mem L α⟩

variable (τ) in
@[expose] def torusTangent (i : Fin τ.rank) :
    TangentSpace L (realizedCoord τ L) (Bialgebra.counitAlgHom L (realizedCoord τ L)) :=
  ⟨_, torusTangent_mem L i⟩

theorem rootTangent_mk (α : Fin τ.rank → ℤ) (a b : Label τ) :
    (rootTangent τ L α : realizedCoord τ L →ₗ[L] L)
        (Ideal.Quotient.mk _ (glEntry L (Label τ) a b)) =
      pinnedE τ L α (Finsupp.single b 1) a := by
  have hε : ((Polynomial.aeval (DualNumber.eps : DualNumber L) :
      Polynomial L →ₐ[L] DualNumber L) : Polynomial L →+* DualNumber L) Polynomial.X =
        DualNumber.eps :=
    Polynomial.aeval_X _
  rw [rootTangent, dualTangent_realizedWordCo_mk, mapWord_pinnedWord, wordUnit_pinnedWord,
    hε, pinnedX_of_mul_self_eq_zero α DualNumber.eps_mul_eps, snd_one_add_eps_smul_apply,
    fst_apply_of_baseChange (baseChange_pinnedE _ α)]

theorem torusTangent_mk (i : Fin τ.rank) (a b : Label τ) :
    (torusTangent τ L i : realizedCoord τ L →ₗ[L] L)
        (Ideal.Quotient.mk _ (glEntry L (Label τ) a b)) =
      tangentH τ L i (Finsupp.single b 1) a := by
  have hu : ((Units.map ((torusDualPoint L : TorusAffine L 1 0 →ₐ[L] DualNumber L) :
      TorusAffine L 1 0 →+* DualNumber L).toMonoidHom (torusUnit L 1 0 0) :
        (DualNumber L)ˣ) : DualNumber L) = 1 + DualNumber.eps := by
    simp [coe_torusUnit, torusDualPoint_torusCoord]
  rw [torusTangent, dualTangent_realizedWordCo_mk, mapWord_torusWord, wordUnit_torusWord,
    torusElt_of_eq_one_add i hu DualNumber.eps_mul_eps, snd_one_add_eps_smul_apply,
    fst_apply_of_baseChange (baseChange_tangentH _ i)]

private def pointDual {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (x : B →ₐ[k] k) (E : TangentSpace k B x) : B →ₐ[k] DualNumber k where
  toFun a := ((x a, E.1 a) : DualNumber k)
  map_one' := by
    apply TrivSqZeroExt.ext
    · change x 1 = 1
      rw [map_one]
    · change E.1 1 = 0
      exact map_one_of_mem_tangentSpace E.2
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change x (a * b) = x a * x b
      rw [map_mul]
    · change E.1 (a * b) = x a * E.1 b + E.1 a * x b
      rw [mul_comm (E.1 a) (x b)]
      exact E.2 a b
  map_zero' := by
    apply TrivSqZeroExt.ext <;> change _ = 0 <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext <;> change _ = _ + _ <;> simp
  commutes' r := by
    apply TrivSqZeroExt.ext
    · exact x.commutes r
    · change E.1 (algebraMap k B r) = 0
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one_of_mem_tangentSpace E.2, smul_zero]

@[simp] private theorem pointDual_apply {k : Type} [Field k] {B : Type} [CommRing B]
    [Algebra k B] (x : B →ₐ[k] k) (E : TangentSpace k B x) (a : B) :
    pointDual x E a = ((x a, E.1 a) : DualNumber k) := rfl

omit [IsAlgClosed L] in
theorem tangentEntries_injective (x : realizedCoord τ L →ₐ[L] L) :
    Function.Injective (tangentEntries x) := by
  intro D D' h
  have hsub : tangentEntries x (D - D') = 0 := by
    rw [map_sub, h, sub_self]
  have hE : ∀ a b : Label τ,
      (D - D').1 (Ideal.Quotient.mk _ (glEntry L (Label τ) a b)) = 0 := by
    intro a b
    have := congrArg (fun M : Matrix (Label τ) (Label τ) L => M a b) hsub
    simpa [tangentEntries_apply] using this
  let E : TangentSpace L (realizedCoord τ L) x := D - D'
  let Φ : realizedCoord τ L →ₐ[L] DualNumber L := pointDual x E
  have hΦ : Φ.comp (Ideal.Quotient.mkₐ L (subgroupIdeal (adjointPointSubgroup τ L))) =
      (Algebra.ofId L (DualNumber L)).comp
        (x.comp (Ideal.Quotient.mkₐ L (subgroupIdeal (adjointPointSubgroup τ L)))) := by
    refine GLCoord.algHom_ext_of_entries fun a b => ?_
    simp only [AlgHom.comp_apply, Φ, pointDual_apply, Algebra.ofId_apply]
    rw [show E.1 ((Ideal.Quotient.mkₐ L _) (glEntry L (Label τ) a b)) = 0 from hE a b]
    rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.inl]
    rfl
  have hzero : ∀ a, E.1 (Ideal.Quotient.mk _ a) = 0 := by
    intro a
    have h2 := congrArg (fun (f : GLCoord L (Label τ) →ₐ[L] DualNumber L) => f a) hΦ
    simp only [AlgHom.comp_apply, Φ, pointDual_apply, Algebra.ofId_apply] at h2
    have h3 := congrArg TrivSqZeroExt.snd h2
    simpa [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.inl] using h3
  have hE0 : E = 0 := by
    refine Subtype.ext (LinearMap.ext fun q => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact hzero a
  simpa using sub_eq_zero.1 hE0

omit
  [IsAlgClosed L] in
private theorem rootDiag_apply (a : Fin τ.rank → Lˣ) (v : RootModule τ L) :
    rootDiag a v =
      Finset.sum v.support fun b =>
        v b • ((rootChar a (labelWt τ b) : L) • Finsupp.single b 1) := by
  let f : Label τ → RootModule τ L := fun b => match b with
    | Sum.inl i => hVec τ L i
    | Sum.inr α =>
        ((∏ i, (a i) ^ (α : Fin τ.rank → ℤ) i : Lˣ) : L) • Finsupp.single (Sum.inr α) 1
  have hf : rootDiag a = Finsupp.linearCombination L f := rfl
  rw [hf, Finsupp.linearCombination_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb : f b = (rootChar a (labelWt τ b) : L) • Finsupp.single b 1 := by
    rw [← rootDiag_single a b]
    rw [hf, Finsupp.linearCombination_single]
    simp
  change v b • f b = v b • ((rootChar a (labelWt τ b) : L) • Finsupp.single b 1)
  rw [hb]

omit
  [IsAlgClosed L] in
private theorem rootChar_inv (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar a⁻¹ v = (rootChar a v)⁻¹ := by
  rw [show rootChar a⁻¹ v = rootChar a (-v) from by
    simp [rootChar, zpow_neg]]
  rw [show -v = 0 - v from by simp, rootChar_sub, rootChar_zero, one_mul]

omit
  [IsAlgClosed L] in
private theorem rootDiag_conj_entry (a : Fin τ.rank → Lˣ) (e : ModGL τ L)
    (a' b' : Label τ) :
    ((rootDiag a * (e : Module.End L (RootModule τ L)) * rootDiag a⁻¹)
      (Finsupp.single b' 1)) a' =
      (rootChar a (labelWt τ a' - labelWt τ b') : L) *
        ((e : Module.End L (RootModule τ L)) (Finsupp.single b' 1) a') := by
  have hd : rootDiag a⁻¹ (Finsupp.single b' 1) =
      (rootChar a⁻¹ (labelWt τ b') : L) • Finsupp.single b' 1 := by
    rw [rootDiag_apply, Finset.sum_eq_single b']
    · simp
    · intro c _ hc
      simp [Finsupp.single_eq_of_ne hc]
    · intro hb
      simp at hb
  rw [Module.End.mul_apply, Module.End.mul_apply, hd, map_smul, map_smul]
  change (rootChar a⁻¹ (labelWt τ b') : L) *
      ((rootDiag a ((e : Module.End L (RootModule τ L)) (Finsupp.single b' 1))) a') =
    (rootChar a (labelWt τ a' - labelWt τ b') : L) *
      ((e : Module.End L (RootModule τ L)) (Finsupp.single b' 1) a')
  rw [rootDiag_apply]
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single a']
  · simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    have h1 : (rootChar a⁻¹ (labelWt τ b') : L) = ((rootChar a (labelWt τ b'))⁻¹ : L) := by
      rw [rootChar_inv L a (labelWt τ b'), Units.val_inv_eq_inv_val]
    have h2 : (rootChar a (labelWt τ a' - labelWt τ b') : L) =
        (rootChar a (labelWt τ a') : L) * ((rootChar a (labelWt τ b'))⁻¹ : L) := by
      rw [rootChar_sub, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [h1, h2]
    ring
  · intro c _ hc
    simp [Finsupp.single_eq_of_ne (Ne.symm hc)]
  · intro ha
    rw [Finsupp.notMem_support_iff.1 ha]
    simp

open scoped CFSG.ConvolutionPoints in
private theorem innerCo_rootDiagUnit_glEntry (a : Fin τ.rank → Lˣ) (a' b' : Label τ) :
    innerCo (modGLPoint τ L (rootDiagUnit τ a)) (glEntry L (Label τ) a' b') =
      (rootChar a (labelWt τ a' - labelWt τ b') : L) • glEntry L (Label τ) a' b' := by
  apply sub_eq_zero.1
  refine eq_zero_of_forall_algHom L (GLCoord L (Label τ)) _ fun y => ?_
  rw [map_sub, sub_eq_zero]
  let e : ModGL τ L := (modGLPoint τ L).symm (toConv y)
  have hy : (modGLPoint τ L e).ofConv = y := by
    rw [MulEquiv.apply_symm_apply, ofConv_toConv]
  rw [← hy]
  have h1 : ((modGLPoint τ L e).ofConv) (innerCo (modGLPoint τ L (rootDiagUnit τ a))
      (glEntry L (Label τ) a' b')) =
      (toConv ((modGLPoint τ L e).ofConv.comp
        (innerCo (modGLPoint τ L (rootDiagUnit τ a))))) (glEntry L (Label τ) a' b') := rfl
  rw [h1, point_comp_innerCo]
  have hmap : modGLPoint τ L (rootDiagUnit τ a) * modGLPoint τ L e *
      (modGLPoint τ L (rootDiagUnit τ a))⁻¹ =
      modGLPoint τ L (rootDiagUnit τ a * e * (rootDiagUnit τ a)⁻¹) := by
    apply (modGLPoint τ L).symm.injective
    simp only [map_mul, MulEquiv.symm_apply_apply, MulEquiv.map_inv]
  refine Eq.trans (b := ((modGLPoint τ L (rootDiagUnit τ a * e *
      (rootDiagUnit τ a)⁻¹)).ofConv (glEntry L (Label τ) a' b'))) ?_ ?_
  · let F : WithConv (GLCoord L (Label τ) →ₐ[L] L) → L := fun φ =>
      φ.ofConv (glEntry L (Label τ) a' b')
    exact congrArg F hmap
  · rw [modGLPoint_apply_glEntry, map_smul, modGLPoint_apply_glEntry, smul_eq_mul]
    simpa [rootDiagUnit, rootDiagUnit_inv] using rootDiag_conj_entry L a e a' b'

private theorem innerCo_rootDiagUnit_glEntry' (a : Fin τ.rank → Lˣ) (a' b' : Label τ) :
    innerCo ((modGLPoint τ L).toMonoidHom (rootDiagUnit τ a)) (glEntry L (Label τ) a' b') =
      (rootChar a (labelWt τ a' - labelWt τ b') : L) • glEntry L (Label τ) a' b' := by
  simpa using innerCo_rootDiagUnit_glEntry L a a' b'

theorem adTangent_rootDiagUnit_rootTangent {a : Fin τ.rank → Lˣ}
    (ha : rootDiagUnit τ a ∈ adjointGroup τ L) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    adTangent (adjointPointSubgroup τ L)
        (Subgroup.mem_map_of_mem (modGLPoint τ L).toMonoidHom ha) (rootTangent τ L α) =
      (rootChar a α : L) • rootTangent τ L α := by
  refine tangentEntries_injective (L := L) (Bialgebra.counitAlgHom L (realizedCoord τ L)) ?_
  ext a' b'
  rw [tangentEntries_apply, tangentEntries_apply]
  unfold adTangent
  rw [coe_tangentMap]
  rw [LinearMap.comp_apply]
  have hq : ∀ (h : ∀ y ∈ subgroupPoints (adjointPointSubgroup τ L),
      y.comp (innerCo ((modGLPoint τ L).toMonoidHom (rootDiagUnit τ a))) ∈
        subgroupPoints (adjointPointSubgroup τ L)),
      (quotientCo (adjointPointSubgroup τ L)
        (innerCo ((modGLPoint τ L).toMonoidHom (rootDiagUnit τ a))) h)
        (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
          (glEntry L (Label τ) a' b')) =
      Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
        (innerCo ((modGLPoint τ L).toMonoidHom (rootDiagUnit τ a))
          (glEntry L (Label τ) a' b')) :=
    fun h => rfl
  rw [AlgHom.toLinearMap_apply, hq]
  rw [innerCo_rootDiagUnit_glEntry']
  change (rootTangent τ L α).1 ((rootChar a (labelWt τ a' - labelWt τ b') : L) •
      (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
        (glEntry L (Label τ) a' b'))) =
    ((↑(rootChar a α) : L) • rootTangent τ L α).1
      ((Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
        (glEntry L (Label τ) a' b')))
  have hsm : (rootTangent τ L α).1 ((rootChar a (labelWt τ a' - labelWt τ b') : L) •
      (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
        (glEntry L (Label τ) a' b'))) =
      ((rootChar a (labelWt τ a' - labelWt τ b') : L) : L) * (rootTangent τ L α).1
        (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
          (glEntry L (Label τ) a' b')) := by
    rw [map_smul, smul_eq_mul]
  rw [hsm]
  change (rootChar a (labelWt τ a' - labelWt τ b') : L) * (rootTangent τ L α).1
      (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L)) (glEntry L (Label τ) a' b')) =
    ((↑(rootChar a α) : L) • rootTangent τ L α).1
      (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L)) (glEntry L (Label τ) a' b'))
  rw [rootTangent_mk]
  rw [Submodule.coe_smul]
  rw [LinearMap.smul_apply, rootTangent_mk]
  by_cases h : pinnedE τ L α (Finsupp.single b' 1) a' = 0
  · simp [h]
  · have hwt : labelWt τ a' = labelWt τ b' + α := by
      have hs : ((rootOperatorFamily τ).pinnedFamilySign α : L) ≠ 0 := by
        rcases (rootOperatorFamily τ).pinnedFamilySign_eq α with h' | h' <;> rw [h'] <;> norm_num
      have hD : (rootOperatorFamily τ).D L ⟨α, hα⟩ 1 (Finsupp.single b' 1) a' ≠ 0 := by
        intro h0
        apply h
        rw [(rootOperatorFamily τ).pinnedE_eq_smul_D L hα]
        change ((rootOperatorFamily τ).pinnedFamilySign α : L) *
          ((rootOperatorFamily τ).D L ⟨α, hα⟩ 1) (Finsupp.single b' 1) a' = 0
        rw [h0, mul_zero]
      simpa using (rootOperatorFamily τ).D_weight_shift ⟨α, hα⟩
        (show 1 ≤ 1 by norm_num) a' b' hD
    rw [show labelWt τ a' - labelWt τ b' = α from by rw [hwt, add_sub_cancel_left]]
    rw [smul_eq_mul]

omit
  [IsAlgClosed L] in
private theorem tangentH_single_of_ne {i : Fin τ.rank} {a' b' : Label τ} (h : a' ≠ b') :
    tangentH τ L i (Finsupp.single b' 1) a' = 0 := by
  rw [tangentH, Finsupp.linearCombination_single]
  rcases b' with j | ⟨α, hα⟩
  · simp
  · rw [one_smul, Finsupp.smul_apply]
    have h0 : (Finsupp.single (Sum.inr ⟨α, hα⟩) 1 : Label τ →₀ L) a' = 0 :=
      Finsupp.single_eq_of_ne h
    rw [h0, smul_zero]

theorem adTangent_rootDiagUnit_torusTangent {a : Fin τ.rank → Lˣ}
    (ha : rootDiagUnit τ a ∈ adjointGroup τ L) (i : Fin τ.rank) :
    adTangent (adjointPointSubgroup τ L)
        (Subgroup.mem_map_of_mem (modGLPoint τ L).toMonoidHom ha) (torusTangent τ L i) =
      torusTangent τ L i := by
  refine tangentEntries_injective (L := L) (Bialgebra.counitAlgHom L (realizedCoord τ L)) ?_
  ext a' b'
  rw [tangentEntries_apply, tangentEntries_apply]
  unfold adTangent
  rw [coe_tangentMap, LinearMap.comp_apply]
  have hq : ∀ (h : ∀ y ∈ subgroupPoints (adjointPointSubgroup τ L),
      y.comp (innerCo ((modGLPoint τ L).toMonoidHom (rootDiagUnit τ a))) ∈
        subgroupPoints (adjointPointSubgroup τ L)),
      (quotientCo (adjointPointSubgroup τ L)
        (innerCo ((modGLPoint τ L).toMonoidHom (rootDiagUnit τ a))) h)
        (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
          (glEntry L (Label τ) a' b')) =
      Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
        (innerCo ((modGLPoint τ L).toMonoidHom (rootDiagUnit τ a))
          (glEntry L (Label τ) a' b')) :=
    fun h => rfl
  rw [AlgHom.toLinearMap_apply, hq, innerCo_rootDiagUnit_glEntry']
  have hsm : (torusTangent τ L i).1 ((rootChar a (labelWt τ a' - labelWt τ b') : L) •
      (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
        (glEntry L (Label τ) a' b'))) =
      (rootChar a (labelWt τ a' - labelWt τ b') : L) * (torusTangent τ L i).1
        (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L))
          (glEntry L (Label τ) a' b')) := by
    rw [map_smul, smul_eq_mul]
  change (torusTangent τ L i).1 ((rootChar a (labelWt τ a' - labelWt τ b') : L) •
      (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L)) (glEntry L (Label τ) a' b'))) =
    (torusTangent τ L i).1
      (Ideal.Quotient.mk (subgroupIdeal (adjointPointSubgroup τ L)) (glEntry L (Label τ) a' b'))
  rw [hsm]
  rw [torusTangent_mk]
  by_cases h : a' = b'
  · subst h
    rw [sub_self, rootChar_zero]
    simp
  · have h0 : tangentH τ L i (Finsupp.single b' 1) a' = 0 := tangentH_single_of_ne L h
    rw [h0, mul_zero]

end CFSG.LieType.AlgebraicGroups

end
