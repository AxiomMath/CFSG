module

public import CFSG.LieType.Chevalley.GraphFixedF4GroupTorus
public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner
public import CFSG.LieType.Chevalley.GraphFixedSimplePairs
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.GraphFixedNoncentralSolvable
public import CFSG.LieType.Chevalley.SingleEdgePerfect
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.Adjoint (BaseChange)

theorem f4LabelRep_injective
    : Function.Injective f4LabelRep :=
  Function.LeftInverse.injective e6LabelToF4_f4LabelRep

section Inverse

variable (K : Type*) [CommRing K]

@[expose] def e6ToF4Module
    : RootModule Tag.E6 K →ₗ[K] RootModule Tag.F4 K :=
  Finsupp.lcomapDomain f4LabelRep f4LabelRep_injective

variable {K} in
theorem e6ToF4Module_apply
    (v : RootModule Tag.E6 K) (a : Label Tag.F4) :
    e6ToF4Module K v a = v (f4LabelRep a) :=
  rfl

theorem e6ToF4Module_comp_f4ToE6Module :
    e6ToF4Module K ∘ₗ f4ToE6Module K = LinearMap.id := by
  ext w a
  simp only [LinearMap.comp_apply, e6ToF4Module_apply, f4ToE6Module_apply,
    e6LabelToF4_f4LabelRep, LinearMap.id_apply]

end Inverse

section Field

variable (K : Type) [Field K]

theorem f4ToE6Module_mem
    (w : RootModule Tag.F4 K) : f4ToE6Module K w ∈ e6GraphFixedModule K := by
  rw [← range_f4ToE6Module]
  exact LinearMap.mem_range_self _ w

variable {K} in
theorem f4ToE6Module_e6ToF4Module
    {v : RootModule Tag.E6 K} (hv : v ∈ e6GraphFixedModule K) :
    f4ToE6Module K (e6ToF4Module K v) = v := by
  have hv' : ∀ b, v (e6LabelPerm b) = v b := fun b => by
    have h := congrArg (fun u : RootModule Tag.E6 K => u (e6LabelPerm b))
      (mem_e6GraphFixedModule.1 hv)
    simp only [e6DiagramEnd_apply, Equiv.symm_apply_apply] at h
    exact h.symm
  ext b
  rw [f4ToE6Module_apply, e6ToF4Module_apply]
  rcases f4LabelRep_e6LabelToF4 b with h | h
  · rw [h]
  · rw [h, hv']

@[expose] def e6RestrictEnd
    (A : Module.End K (RootModule Tag.E6 K)) :
    Module.End K (RootModule Tag.F4 K) :=
  e6ToF4Module K ∘ₗ A ∘ₗ f4ToE6Module K

variable {K} in
theorem f4ToE6Module_comp_e6RestrictEnd
    {A : Module.End K (RootModule Tag.E6 K)}
    (hA : ∀ v ∈ e6GraphFixedModule K, A v ∈ e6GraphFixedModule K) :
    f4ToE6Module K ∘ₗ e6RestrictEnd K A = A ∘ₗ f4ToE6Module K :=
  LinearMap.ext fun w => f4ToE6Module_e6ToF4Module (hA _ (f4ToE6Module_mem K w))

theorem e6RestrictEnd_one
    : e6RestrictEnd K 1 = 1 := by
  change e6ToF4Module K ∘ₗ LinearMap.id ∘ₗ f4ToE6Module K = LinearMap.id
  rw [LinearMap.id_comp, e6ToF4Module_comp_f4ToE6Module]

variable {K} in
theorem e6RestrictEnd_mul
    (A : Module.End K (RootModule Tag.E6 K))
    {B : Module.End K (RootModule Tag.E6 K)}
    (hB : ∀ v ∈ e6GraphFixedModule K, B v ∈ e6GraphFixedModule K) :
    e6RestrictEnd K (A * B) = e6RestrictEnd K A * e6RestrictEnd K B := by
  refine LinearMap.ext fun w => ?_
  simp only [e6RestrictEnd, LinearMap.comp_apply, Module.End.mul_apply]
  rw [f4ToE6Module_e6ToF4Module (hB _ (f4ToE6Module_mem K w))]

variable {K} in
theorem apply_mem_e6GraphFixedModule_of_commute {A : Module.End K (RootModule Tag.E6 K)}
    (hA : e6DiagramEnd K * A = A * e6DiagramEnd K) {v : RootModule Tag.E6 K}
    (hv : v ∈ e6GraphFixedModule K) : A v ∈ e6GraphFixedModule K := by
  rw [mem_e6GraphFixedModule] at hv ⊢
  rw [← Module.End.mul_apply, hA, Module.End.mul_apply, hv]

@[expose] def e6EndHom : ModGL TwistTag.E6.tag K →* Module.End K (RootModule Tag.E6 K) :=
  Units.coeHom _

theorem e6EndHom_diagramMap : e6EndHom K (diagramMap TwistTag.E6 K) = e6DiagramEnd K :=
  rfl

variable {K} in
theorem diagramMap_mul_of_mem_twistedFixedGroup {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    diagramMap TwistTag.E6 K * g = g * diagramMap TwistTag.E6 K := by
  have h := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (RingHom.id K)).1 hg).2
  rw [twistHom_apply, show Units.map (entrywiseHom (RingHom.id K)) g = g from
    Units.ext (entrywise_id _)] at h
  calc diagramMap TwistTag.E6 K * g =
        diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ * diagramMap TwistTag.E6 K := by
        group
    _ = g * diagramMap TwistTag.E6 K := by rw [h]

variable {K} in
theorem mem_twistedFixedGroup_id_iff {g : ModGL TwistTag.E6.tag K} :
    g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) ↔
      g ∈ adjointGroup TwistTag.E6.tag K ∧
        diagramMap TwistTag.E6 K * g = g * diagramMap TwistTag.E6 K := by
  refine ⟨fun hg => ⟨hg.1, diagramMap_mul_of_mem_twistedFixedGroup hg⟩, fun ⟨hC, hP⟩ => ⟨hC, ?_⟩⟩
  change twistHom TwistTag.E6 K (RingHom.id K) g = g
  rw [twistHom_apply, show Units.map (entrywiseHom (RingHom.id K)) g = g from
    Units.ext (entrywise_id _), hP, mul_inv_cancel_right]

variable {K} in
theorem e6DiagramEnd_mul_e6EndHom {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    e6DiagramEnd K * e6EndHom K g = e6EndHom K g * e6DiagramEnd K := by
  have h := congrArg (e6EndHom K) (diagramMap_mul_of_mem_twistedFixedGroup hg)
  rwa [map_mul, map_mul, e6EndHom_diagramMap] at h

variable {K} in
theorem e6EndHom_apply_mem {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)) {v : RootModule Tag.E6 K}
    (hv : v ∈ e6GraphFixedModule K) : e6EndHom K g v ∈ e6GraphFixedModule K :=
  apply_mem_e6GraphFixedModule_of_commute (e6DiagramEnd_mul_e6EndHom hg) hv

variable {K} in
theorem e6RestrictEnd_mul_inv
    (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    e6RestrictEnd K (e6EndHom K g) * e6RestrictEnd K (e6EndHom K (g⁻¹ :
      twistedFixedGroup TwistTag.E6 K (RingHom.id K))) = 1 := by
  rw [← e6RestrictEnd_mul _ fun v hv => e6EndHom_apply_mem (g⁻¹).2 hv, ← map_mul,
    ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_one, e6RestrictEnd_one]

@[expose] def e6FixedToF4
    : twistedFixedGroup TwistTag.E6 K (RingHom.id K) →* ModGL Tag.F4 K where
  toFun g :=
    { val := e6RestrictEnd K (e6EndHom K g)
      inv := e6RestrictEnd K (e6EndHom K (g⁻¹ : twistedFixedGroup TwistTag.E6 K (RingHom.id K)))
      val_inv := e6RestrictEnd_mul_inv g
      inv_val := by
        have h := e6RestrictEnd_mul_inv g⁻¹
        rwa [inv_inv] at h }
  map_one' := Units.ext (by
    change e6RestrictEnd K (e6EndHom K ((1 : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
      ModGL TwistTag.E6.tag K)) = 1
    rw [Subgroup.coe_one, map_one, e6RestrictEnd_one])
  map_mul' g h := Units.ext (by
    change e6RestrictEnd K (e6EndHom K ((g * h : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
      ModGL TwistTag.E6.tag K)) = e6RestrictEnd K (e6EndHom K g) * e6RestrictEnd K (e6EndHom K h)
    rw [Subgroup.coe_mul, map_mul]
    exact e6RestrictEnd_mul _ fun v hv => e6EndHom_apply_mem h.2 hv)

variable {K} in
theorem coe_e6FixedToF4
    (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    (e6FixedToF4 K g : Module.End K (RootModule Tag.F4 K)) = e6RestrictEnd K (e6EndHom K g) :=
  rfl

variable {K} in
theorem f4ToE6Module_comp_e6FixedToF4
    (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    f4ToE6Module K ∘ₗ (e6FixedToF4 K g : Module.End K (RootModule Tag.F4 K)) =
      e6EndHom K g ∘ₗ f4ToE6Module K :=
  f4ToE6Module_comp_e6RestrictEnd fun _ hv => e6EndHom_apply_mem g.2 hv

@[expose] def f4FoldedIndex : Fin Tag.F4.rank → Fin TwistTag.E6.foldedTag.rank :=
  (![⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩] :
    Fin 4 → Fin TwistTag.E6.foldedTag.rank)

@[expose] def f4UnfoldIndex : Fin TwistTag.E6.foldedTag.rank → Fin Tag.F4.rank :=
  (![⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩] : Fin 4 → Fin Tag.F4.rank)

theorem f4FoldedIndex_f4UnfoldIndex (a : Fin TwistTag.E6.foldedTag.rank) :
    f4FoldedIndex (f4UnfoldIndex a) = a := by
  fin_cases a <;> rfl

@[expose] def f4OrbitXUnit
    (j : Fin Tag.F4.rank) (c : K) : ModGL TwistTag.E6.tag K :=
  ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map fun i => xUnit TwistTag.E6.tag K i c).prod

@[expose] def f4OrbitYUnit
    (j : Fin Tag.F4.rank) (c : K) : ModGL TwistTag.E6.tag K :=
  ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map fun i => yUnit TwistTag.E6.tag K i c).prod

variable {K} in
theorem e6EndHom_f4OrbitXUnit
    (j : Fin Tag.F4.rank) (c : K) :
    e6EndHom K (f4OrbitXUnit K j c) = f4OrbitX K j c := by
  rw [f4OrbitXUnit, map_list_prod, List.map_map]
  fin_cases j <;> rfl

variable {K} in
theorem e6EndHom_f4OrbitYUnit
    (j : Fin Tag.F4.rank) (c : K) :
    e6EndHom K (f4OrbitYUnit K j c) = f4OrbitY K j c := by
  rw [f4OrbitYUnit, map_list_prod, List.map_map]
  fin_cases j <;> rfl

variable {K} in
theorem ringHom_id_pow_apply (k : ℕ) (c : K) : (RingHom.id K ^ k) c = c := by
  rw [show RingHom.id K = 1 from rfl, one_pow]
  rfl

variable {K} in
theorem mem_orbitField_id (a : Fin TwistTag.E6.foldedTag.rank) (c : K) :
    c ∈ orbitField TwistTag.E6 K (RingHom.id K) a :=
  mem_orbitField.2 (ringHom_id_pow_apply _ c)

variable {K} in
theorem coe_orbitX_id_eq_prod
    (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K (RingHom.id K) a) :
    (orbitX TwistTag.E6 K (RingHom.id K) a c : ModGL TwistTag.E6.tag K) =
      ((TwistTag.E6.orbitWord a).map fun i => xUnit TwistTag.E6.tag K i c).prod := by
  rw [coe_orbitX, TwistTag.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, ringHom_id_pow_apply]

variable {K} in
theorem coe_orbitY_id_eq_prod
    (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K (RingHom.id K) a) :
    (orbitY TwistTag.E6 K (RingHom.id K) a c : ModGL TwistTag.E6.tag K) =
      ((TwistTag.E6.orbitWord a).map fun i => yUnit TwistTag.E6.tag K i c).prod := by
  rw [coe_orbitY, TwistTag.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, ringHom_id_pow_apply]

variable {K} in
theorem coe_orbitX_id
    (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K (RingHom.id K) a) :
    (orbitX TwistTag.E6 K (RingHom.id K) a c : ModGL TwistTag.E6.tag K) =
      f4OrbitXUnit K (f4UnfoldIndex a) c := by
  rw [coe_orbitX_id_eq_prod, f4OrbitXUnit, f4FoldedIndex_f4UnfoldIndex]

variable {K} in
theorem coe_orbitY_id
    (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K (RingHom.id K) a) :
    (orbitY TwistTag.E6 K (RingHom.id K) a c : ModGL TwistTag.E6.tag K) =
      f4OrbitYUnit K (f4UnfoldIndex a) c := by
  rw [coe_orbitY_id_eq_prod, f4OrbitYUnit, f4FoldedIndex_f4UnfoldIndex]

variable {K} in
theorem f4OrbitXUnit_eq_orbitX
    (j : Fin Tag.F4.rank) (c : K) :
    f4OrbitXUnit K j c = (orbitX TwistTag.E6 K (RingHom.id K) (f4FoldedIndex j)
      ⟨c, mem_orbitField_id _ c⟩ : ModGL TwistTag.E6.tag K) := by
  rw [coe_orbitX_id_eq_prod, f4OrbitXUnit]

variable {K} in
theorem f4OrbitYUnit_eq_orbitY
    (j : Fin Tag.F4.rank) (c : K) :
    f4OrbitYUnit K j c = (orbitY TwistTag.E6 K (RingHom.id K) (f4FoldedIndex j)
      ⟨c, mem_orbitField_id _ c⟩ : ModGL TwistTag.E6.tag K) := by
  rw [coe_orbitY_id_eq_prod, f4OrbitYUnit]

variable {K} in
theorem f4OrbitXUnit_mem
    (j : Fin Tag.F4.rank) (c : K) :
    f4OrbitXUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  rw [f4OrbitXUnit_eq_orbitX]
  exact graphFixedPosUnipotent_le _ _ _ (orbitX_mem_graphFixedPosUnipotent _ _ _ _)

variable {K} in
theorem f4OrbitYUnit_mem
    (j : Fin Tag.F4.rank) (c : K) :
    f4OrbitYUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  rw [f4OrbitYUnit_eq_orbitY]
  exact graphFixedNegUnipotent_le _ _ _ (orbitY_mem_graphFixedNegUnipotent _ _ _ _)

variable {K}

theorem e6FixedToF4_f4OrbitXUnit
    (h2 : (2 : K) = 0) (j : Fin Tag.F4.rank) (c : K) :
    e6FixedToF4 K ⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩ = xUnit Tag.F4 K j c := by
  refine Units.ext ?_
  rw [coe_e6FixedToF4, coe_xUnit, e6RestrictEnd]
  change e6ToF4Module K ∘ₗ e6EndHom K (f4OrbitXUnit K j c) ∘ₗ f4ToE6Module K = _
  rw [e6EndHom_f4OrbitXUnit, f4OrbitX_comp_f4ToE6Module K h2 j c, ← LinearMap.comp_assoc,
    e6ToF4Module_comp_f4ToE6Module, LinearMap.id_comp]

theorem e6FixedToF4_f4OrbitYUnit
    (h2 : (2 : K) = 0) (j : Fin Tag.F4.rank) (c : K) :
    e6FixedToF4 K ⟨f4OrbitYUnit K j c, f4OrbitYUnit_mem j c⟩ = yUnit Tag.F4 K j c := by
  refine Units.ext ?_
  rw [coe_e6FixedToF4, coe_yUnit, e6RestrictEnd]
  change e6ToF4Module K ∘ₗ e6EndHom K (f4OrbitYUnit K j c) ∘ₗ f4ToE6Module K = _
  rw [e6EndHom_f4OrbitYUnit, f4OrbitY_comp_f4ToE6Module K h2 j c, ← LinearMap.comp_assoc,
    e6ToF4Module_comp_f4ToE6Module, LinearMap.id_comp]

theorem twistedFixedGroup_id_eq_closure :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) = Subgroup.closure
      {g | ∃ (j : Fin Tag.F4.rank) (c : K), g = f4OrbitXUnit K j c ∨ g = f4OrbitYUnit K j c} := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · rw [e6_twistedFixedGroup_id_eq_graphFixedRootGroup,
      graphFixedRootGroup_eq_iSup_orbitRankOneGroup (σ := RingHom.id K) (fun x => ⟨x, rfl⟩)]
    refine iSup_le fun a => (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact Subgroup.subset_closure ⟨f4UnfoldIndex a, c, Or.inl (coe_orbitX_id a c)⟩
    · exact Subgroup.subset_closure ⟨f4UnfoldIndex a, c, Or.inr (coe_orbitY_id a c)⟩
  · rintro _ ⟨j, c, rfl | rfl⟩
    exacts [f4OrbitXUnit_mem j c, f4OrbitYUnit_mem j c]

theorem e6FixedToF4_mem_adjointGroup
    (h2 : (2 : K) = 0)
    (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    e6FixedToF4 K g ∈ adjointGroup Tag.F4 K := by
  set H := (adjointGroup Tag.F4 K).comap (e6FixedToF4 K)
  have hle : twistedFixedGroup TwistTag.E6 K (RingHom.id K) ≤
      H.map (twistedFixedGroup TwistTag.E6 K (RingHom.id K)).subtype := by
    conv_lhs => rw [twistedFixedGroup_id_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, c, rfl | rfl⟩
    · refine ⟨⟨_, f4OrbitXUnit_mem j c⟩, ?_, rfl⟩
      change e6FixedToF4 K ⟨_, f4OrbitXUnit_mem j c⟩ ∈ adjointGroup Tag.F4 K
      rw [e6FixedToF4_f4OrbitXUnit h2]
      exact xUnit_mem_adjointGroup j c
    · refine ⟨⟨_, f4OrbitYUnit_mem j c⟩, ?_, rfl⟩
      change e6FixedToF4 K ⟨_, f4OrbitYUnit_mem j c⟩ ∈ adjointGroup Tag.F4 K
      rw [e6FixedToF4_f4OrbitYUnit h2]
      exact yUnit_mem_adjointGroup j c
  obtain ⟨h, hh, hgh⟩ := hle g.2
  rw [show g = h from Subtype.ext hgh.symm]
  exact hh

theorem adjointGroup_le_range_e6FixedToF4
    (h2 : (2 : K) = 0) :
    adjointGroup Tag.F4 K ≤ (e6FixedToF4 K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨j, c, hg | hg⟩
  · rw [show g = xUnit Tag.F4 K j c from Units.ext hg]
    exact ⟨_, e6FixedToF4_f4OrbitXUnit h2 j c⟩
  · rw [show g = yUnit Tag.F4 K j c from Units.ext hg]
    exact ⟨_, e6FixedToF4_f4OrbitYUnit h2 j c⟩

variable (K) in
@[expose] def e6FixedToF4Group
    (h2 : (2 : K) = 0) :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) →* adjointGroup Tag.F4 K :=
  (e6FixedToF4 K).codRestrict _ (e6FixedToF4_mem_adjointGroup h2)

theorem e6FixedToF4Group_surjective
    (h2 : (2 : K) = 0) :
    Function.Surjective (e6FixedToF4Group K h2) := fun g => by
  obtain ⟨x, hx⟩ := adjointGroup_le_range_e6FixedToF4 h2 g.2
  exact ⟨x, Subtype.ext hx⟩

theorem nontrivial_adjointGroup_F4
    : Nontrivial (adjointGroup Tag.F4 K) := by
  refine ⟨⟨⟨xUnit Tag.F4 K ⟨0, by decide⟩ 1, xUnit_mem_adjointGroup _ _⟩, 1, fun h => ?_⟩⟩
  have h' : xOp Tag.F4 K ⟨0, by decide⟩ 1 = xOp Tag.F4 K ⟨0, by decide⟩ 0 := by
    rw [xOp_zero]
    exact congrArg (fun g : adjointGroup Tag.F4 K =>
      ((g : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K))) h
  exact one_ne_zero (xOp_injective _ h')

theorem e6FixedToF4Group_injective
    (h2 : (2 : K) = 0) :
    Function.Injective (e6FixedToF4Group K h2) := by
  have hC0 : graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom ≤
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := graphFixedRootGroup_le _ _ _
  set ψ := (e6FixedToF4Group K h2).comp (Subgroup.inclusion hC0)
  have hΓ : ∀ g : twistedFixedGroup TwistTag.E6 K (RingHom.id K),
      (g : ModGL TwistTag.E6.tag K) ∈
        graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom := fun g =>
    (e6_twistedFixedGroup_id_eq_graphFixedRootGroup K).le g.2
  have hψ : Function.Surjective ψ := fun x => by
    obtain ⟨g, rfl⟩ := e6FixedToF4Group_surjective h2 x
    exact ⟨⟨g, hΓ g⟩, rfl⟩
  have hker : ψ.ker = ⊥ := by
    by_contra hne
    have hM : ¬ ψ.ker ≤ Subgroup.center
        (graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom) := by
      rw [center_graphFixedRootGroup_eq_bot (σ := (RingEquiv.refl K).toRingHom)
        (RingEquiv.refl K).surjective]
      exact fun h => hne (le_bot_iff.1 h)
    have := fixed_noncentral_normal_solvable_quotient TwistTag.E6 K (RingEquiv.refl K) ψ.ker hM
    have : Group.IsSolvable (adjointGroup Tag.F4 K) :=
      Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toMonoidHom)
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).surjective
    have := nontrivial_adjointGroup_F4 (K := K)
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (adjointGroup Tag.F4 K)
    rw [single_edge_perfect Tag.F4 K (Or.inl rfl)] at hlt
    exact lt_irrefl _ hlt
  intro g g' hgg'
  have hinj := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  have h : (⟨g, hΓ g⟩ : graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom) =
      ⟨g', hΓ g'⟩ := hinj hgg'
  have h' := congrArg (fun x : graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom =>
    (x : ModGL TwistTag.E6.tag K)) h
  exact Subtype.ext h'

variable (K) in
@[expose] def e6FixedF4Equiv
    (h2 : (2 : K) = 0) :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) ≃* adjointGroup Tag.F4 K :=
  MulEquiv.ofBijective (e6FixedToF4Group K h2)
    ⟨e6FixedToF4Group_injective h2, e6FixedToF4Group_surjective h2⟩

theorem coe_e6FixedF4Equiv
    (h2 : (2 : K) = 0)
    (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    (e6FixedF4Equiv K h2 g : ModGL Tag.F4 K) = e6FixedToF4 K g :=
  rfl

end Field

section BaseChange

variable {K L : Type} [Field K] [Field L] (f : K →+* L)

theorem f4ToE6Module_mapRange
    (w : RootModule Tag.F4 K) :
    f4ToE6Module L (Finsupp.mapRange f f.map_zero w) =
      Finsupp.mapRange f f.map_zero (f4ToE6Module K w) := by
  ext b
  simp only [f4ToE6Module_apply, Finsupp.mapRange_apply]

theorem e6ToF4Module_mapRange
    (v : RootModule Tag.E6 K) :
    e6ToF4Module L (Finsupp.mapRange f f.map_zero v) =
      Finsupp.mapRange f f.map_zero (e6ToF4Module K v) := by
  ext a
  simp only [e6ToF4Module_apply, Finsupp.mapRange_apply]

theorem baseChange_e6RestrictEnd
    {A : Module.End K (RootModule Tag.E6 K)}
    {B : Module.End L (RootModule Tag.E6 L)} (h : BaseChange f A B) :
    BaseChange f (e6RestrictEnd K A) (e6RestrictEnd L B) := fun a => by
  simp only [e6RestrictEnd, LinearMap.comp_apply]
  rw [← e6ToF4Module_mapRange, h.apply, ← f4ToE6Module_mapRange, Finsupp.mapRange_single,
    map_one]

theorem baseChange_e6EndHom
    (g : ModGL TwistTag.E6.tag K) :
    BaseChange f (e6EndHom K g) (e6EndHom L (baseChangeGL f g)) :=
  baseChange_baseChangeEnd f _

theorem baseChangeGL_diagramMap
    (t : TwistTag) :
    baseChangeGL f (diagramMap t K) = diagramMap t L := by
  refine Units.ext ((baseChange_baseChangeEnd f _).unique fun b => ?_)
  simp [diagramMap, Finsupp.mapRange_single]

theorem baseChangeGL_mem_adjointGroup
    {τ : Tag} {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) :
    baseChangeGL f g ∈ adjointGroup τ L := by
  have hle : (adjointGroup τ K).map (baseChangeGL f) ≤ adjointGroup τ L := by
    rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i _, yUnit_mem_adjointGroup i _]
  exact hle (Subgroup.mem_map_of_mem _ hg)

theorem baseChangeGL_mem_twistedFixedGroup
    {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    baseChangeGL f g ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L) := by
  obtain ⟨hC, hP⟩ := mem_twistedFixedGroup_id_iff.1 hg
  refine mem_twistedFixedGroup_id_iff.2 ⟨baseChangeGL_mem_adjointGroup f hC, ?_⟩
  rw [← baseChangeGL_diagramMap f, ← map_mul, hP, map_mul]

theorem e6FixedToF4_baseChangeGL
    (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    e6FixedToF4 L ⟨baseChangeGL f g, baseChangeGL_mem_twistedFixedGroup f g.2⟩ =
      baseChangeGL f (e6FixedToF4 K g) :=
  Units.ext ((baseChange_e6RestrictEnd f (baseChange_e6EndHom f _)).unique
    (baseChange_baseChangeEnd f _))

theorem baseChange_comp {M : Type} [Field M] {f' : L →+* M} {τ : Tag}
    {A : Module.End K (RootModule τ K)} {B : Module.End L (RootModule τ L)}
    {C : Module.End M (RootModule τ M)} (h : BaseChange f A B) (h' : BaseChange f' B C) :
    BaseChange (f'.comp f) A C := fun b => by
  rw [← h' b, ← h b, ← Finsupp.mapRange_comp]
  rfl

theorem baseChangeGL_baseChangeGL
    {M : Type} [Field M] (f' : L →+* M) {τ : Tag}
    (g : ModGL τ K) : baseChangeGL f' (baseChangeGL f g) = baseChangeGL (f'.comp f) g :=
  Units.ext (((baseChange_baseChangeEnd (f'.comp f) _).unique
    (baseChange_comp f (baseChange_baseChangeEnd f _) (baseChange_baseChangeEnd f' _))).symm)

end BaseChange

end CFSG.LieType.Chevalley
