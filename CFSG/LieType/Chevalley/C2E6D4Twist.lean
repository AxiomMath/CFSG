module

public import CFSG.LieType.Chevalley.C2E6D4Faithful
public import CFSG.LieType.Chevalley.C2E6A5CubeTwist

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin

theorem canonicalRep_simple_mem_groupD
    (k : Fin 4) :
    canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).simple (jD k)) ∈ groupD := by
  rw [canonicalRep_simple]
  exact weylElt_mem_subsystemGroup (jD_mem_setD k) 1

theorem psiD_canonicalRep_simple
    (k : Fin 4) :
    psiD ⟨canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).simple (jD k)),
      canonicalRep_simple_mem_groupD k⟩ = weylElt 4 K k := by
  have e : (⟨canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).simple (jD k)),
      canonicalRep_simple_mem_groupD k⟩ : groupD) =
      ⟨xUnit Tag.E6 K (jD k) 1, xUnit_mem_groupD k 1⟩ *
        ⟨yUnit Tag.E6 K (jD k) (-1), yUnit_mem_groupD k (-1)⟩ *
          ⟨xUnit Tag.E6 K (jD k) 1, xUnit_mem_groupD k 1⟩ := by
    apply Subtype.ext
    change canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).simple (jD k)) =
      xUnit Tag.E6 K (jD k) 1 * yUnit Tag.E6 K (jD k) (-1) * xUnit Tag.E6 K (jD k) 1
    rw [canonicalRep_simple, weylElt_eq_xUnit_mul, inv_one, Units.val_one]
  rw [e, map_mul, map_mul, psiD_xUnit, psiD_yUnit]
  rfl

theorem perm_jD_val : ∀ k : Fin 4,
    (TwistTag.E6.perm (jD k)).val = (jD (Equiv.swap 2 3 k)).val := by
  decide

theorem perm_jD (k : Fin 4) : TwistTag.E6.perm (jD k) = jD (Equiv.swap 2 3 k) :=
  Fin.ext (perm_jD_val k)

theorem conj_mem_groupD
    {g : ModGL Tag.E6 K} (hg : g ∈ groupD) :
    diagE6GL * g * diagE6GL⁻¹ ∈ groupD := by
  have hle : groupD ≤ groupD.comap (MulAut.conj diagE6GL).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        diagE6GL_conj_xUnit, perm_jD]
      exact xUnit_mem_groupD _ c
    · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        diagE6GL_conj_yUnit, perm_jD]
      exact yUnit_mem_groupD _ c
  exact hle hg

@[expose] def conjD :
    groupD →* groupD :=
  MonoidHom.mk' (fun g => ⟨diagE6GL * g * diagE6GL⁻¹, conj_mem_groupD g.2⟩) fun g h =>
    Subtype.ext (by
      change diagE6GL * ((g : ModGL Tag.E6 K) * h) * diagE6GL⁻¹ =
        diagE6GL * g * diagE6GL⁻¹ * (diagE6GL * h * diagE6GL⁻¹)
      group)

theorem coe_conjD
    (g : groupD) :
    ((conjD g : groupD) : ModGL Tag.E6 K) = diagE6GL * g * diagE6GL⁻¹ := rfl

theorem psiD_conjD
    (g : groupD) : psiD (conjD g) = swapE4F4 * psiD g * swapE4F4⁻¹ := by
  have key : psiD (conjD g) * swapE4F4 = swapE4F4 * psiD g := by
    refine LinearEquiv.ext fun y => ?_
    obtain ⟨⟨v, hv⟩, rfl⟩ := phiD.surjective y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← phiD_diagramMap hv, psiD_phiD, psiD_phiD,
      ← phiD_diagramMap]
    congr 1
    apply Subtype.ext
    change ((diagE6GL * (g : ModGL Tag.E6 K) * diagE6GL⁻¹ : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) ((diagE6GL : Module.End K (RootModule Tag.E6 K)) v) =
        (diagE6GL : Module.End K (RootModule Tag.E6 K))
          (((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v)
    have hinv : ((diagE6GL⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
        ((diagE6GL : Module.End K (RootModule Tag.E6 K)) v) = v := by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hinv]
  rw [← key, mul_inv_cancel_right]

@[expose] def betaD :
    groupD →* groupD :=
  MonoidHom.mk' (fun g => ⟨betaGL g, betaGL_mem_subsystemGroup g.2⟩) fun g h =>
    Subtype.ext (map_mul betaGL (g : ModGL Tag.E6 K) h)

theorem coe_betaD
    (g : groupD) : ((betaD g : groupD) : ModGL Tag.E6 K) = betaGL g := rfl

theorem labD_injective : Function.Injective labD := fun _ _ e =>
  rootD_injective (congrArg Subtype.val (Sum.inr_injective e))

theorem phiD_apply_natD
    {w : RootModule Tag.E6 K} (hw : w ∈ moduleD) (j : Fin 8) :
    phiD ⟨w, hw⟩ (natD j) = w (labD j) := by
  have key : (LinearMap.proj (natD j) : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] K).comp phiD.toLinearMap =
      (Finsupp.lapply (labD j)).comp moduleD.subtype := by
    refine basisD.ext fun j' => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, basisD_apply, LinearEquiv.coe_coe, phiD_vecD,
      LinearMap.proj_apply, Submodule.subtype_apply, Finsupp.lapply_apply]
    change (Pi.single (natD j') 1 : Fin 4 ⊕ Fin 4 → K) (natD j) =
      rootVec Tag.E6 K (rootD j') (labD j)
    rw [rootVec_eq_single (isRoot_rootD j'), Pi.single_apply, Finsupp.single_apply]
    by_cases h : j' = j
    · subst h
      simp
    · rw [ite_eq_right (natD_injective.ne (Ne.symm h)), ite_eq_right (labD_injective.ne h)]
  exact LinearMap.congr_fun key ⟨w, hw⟩

theorem psiD_single_natD
    (g : groupD) (j j' : Fin 8) :
    psiD g (Pi.single (natD j) 1) (natD j') =
      ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (vecD j) (labD j') := by
  rw [← phiD_vecD j, psiD_phiD, phiD_apply_natD]

theorem psiD_betaD
    (g : groupD) :
    LinearMap.toMatrix' (psiD (betaD g) : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      (LinearMap.toMatrix' (psiD g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))).map bar := by
  ext s t
  obtain ⟨j, rfl⟩ := exists_natD_eq t
  obtain ⟨j', rfl⟩ := exists_natD_eq s
  rw [Matrix.map_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, psiD_single_natD, psiD_single_natD]
  change (entrywise barHom ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)))
    (vecD j) (labD j') = _
  rw [vecD, rootVec_eq_single (isRoot_rootD j), entrywise_single, Finsupp.mapRange_apply]
  rfl

end CFSG.LieType.Chevalley.C2E6Std
