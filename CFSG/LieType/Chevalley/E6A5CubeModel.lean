module

public import CFSG.LieType.Chevalley.C2E6RootRestrictionA
public import CFSG.LieType.Chevalley.C2E6ExteriorCubeKernel
public import CFSG.LinearAlgebra.LinearGroups.Generation

public noncomputable section

namespace CFSG.LieType.Chevalley.E6A5Cube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExteriorCube exteriorPower
  Set Matrix
open CFSG.LieType.Chevalley.C2E6Std (setA jA rootA subsetA eA rootWeight subsetPattern rhoL compRev
  compRevPC isRoot_rootA exists_rootA_eq rootA_one weight_rootA eq_of_weight raise_or lower_or
  raise_rootA lower_rootA raise_subsetA lower_subsetA rootA_ne_single diag_rootA rootA_injective
  eA_val exists_jA_of_mem_setA)
open scoped commutatorElement

variable (K : Type) [Field K]

@[expose] def moduleA : Submodule K (RootModule Tag.E6 K) :=
  Submodule.span K {v | ∃ α, IsRoot Tag.E6 α ∧ α (1 : Fin 6) = 1 ∧ v = rootVec Tag.E6 K α}

abbrev vecA (j : Fin 20) : RootModule Tag.E6 K := rootVec Tag.E6 K (rootA j)

variable {K}

theorem moduleA_eq_span :
    moduleA K = Submodule.span K (Set.range (vecA K)) := by
  rw [moduleA]
  congr 1
  ext v
  constructor
  · rintro ⟨α, hα, h1, rfl⟩
    obtain ⟨j, rfl⟩ := exists_rootA_eq hα h1
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨rootA j, isRoot_rootA j, rootA_one j, rfl⟩

theorem vecA_mem (j : Fin 20) : vecA K j ∈ moduleA K := by
  rw [moduleA_eq_span]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem linearIndependent_vecA : LinearIndependent K (vecA K) := by
  have h := (Finsupp.basisSingleOne (R := K) (ι := Label Tag.E6)).linearIndependent.comp
    (fun j => (Sum.inr ⟨rootA j, isRoot_rootA j⟩ : Label Tag.E6))
    (fun j j' h => rootA_injective (by simpa using h))
  convert h using 1
  funext j
  simp [vecA, C2E6Std.rootVec_eq_single (isRoot_rootA j)]

variable (K) in
@[expose] def basisA : Module.Basis (Fin 20) K (moduleA K) :=
  (Module.Basis.span linearIndependent_vecA).map (LinearEquiv.ofEq _ _ moduleA_eq_span.symm)

theorem basisA_apply (j : Fin 20) :
    basisA K j = ⟨vecA K j, vecA_mem j⟩ := by
  apply Subtype.ext
  simp [basisA, Module.Basis.span_apply]

variable (K) in
@[expose] def phiA : moduleA K ≃ₗ[K] ⋀[K]^3 (Fin 6 → K) :=
  (basisA K).equiv ((Pi.basisFun K (Fin 6)).exteriorPower 3) eA

theorem phiA_vecA (j : Fin 20) :
    phiA K ⟨vecA K j, vecA_mem j⟩ = wedgeBasis (eA j) := by
  rw [← basisA_apply, phiA, Module.Basis.equiv_apply, wedgeBasis_eq_basis]

theorem xOp_vecA
    (j : Fin 20) (t : Fin 5) (c : K) :
    xOp Tag.E6 K (jA t) c (vecA K j) =
      vecA K j + c • rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1) :=
  C2E6Std.xOp_rootVec_E6 (jA t) c (isRoot_rootA j) (rootA_ne_single j t).1 (rootA_ne_single j t).2

theorem yOp_vecA
    (j : Fin 20) (t : Fin 5) (c : K) :
    yOp Tag.E6 K (jA t) c (vecA K j) =
      vecA K j + c • rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1) :=
  C2E6Std.yOp_rootVec_E6 (jA t) c (isRoot_rootA j) (rootA_ne_single j t).1 (rootA_ne_single j t).2

theorem rootVec_raise_mem (j : Fin 20) (t : Fin 5) :
    rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1) ∈ moduleA K := by
  rcases raise_or j t with ⟨j', hj'⟩ | h
  · rw [← hj']
    exact vecA_mem j'
  · rw [C2E6Std.rootVec_eq_zero_of_not h]
    exact Submodule.zero_mem _

theorem rootVec_lower_mem (j : Fin 20) (t : Fin 5) :
    rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1) ∈ moduleA K := by
  rcases lower_or j t with ⟨j', hj'⟩ | h
  · rw [← hj']
    exact vecA_mem j'
  · rw [C2E6Std.rootVec_eq_zero_of_not h]
    exact Submodule.zero_mem _

theorem moduleA_le_comap {f : Module.End K (RootModule Tag.E6 K)}
    (hf : ∀ j, f (vecA K j) ∈ moduleA K) : ∀ v ∈ moduleA K, f v ∈ moduleA K := by
  intro v hv
  have : moduleA K ≤ (moduleA K).comap f := by
    conv_lhs => rw [moduleA_eq_span]
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hf j
  exact this hv

theorem xOp_mem_moduleA
    (t : Fin 5) (c : K) : ∀ v ∈ moduleA K, xOp Tag.E6 K (jA t) c v ∈ moduleA K :=
  moduleA_le_comap fun j => by
    rw [xOp_vecA]
    exact (moduleA K).add_mem (vecA_mem j) ((moduleA K).smul_mem c (rootVec_raise_mem j t))

theorem yOp_mem_moduleA
    (t : Fin 5) (c : K) : ∀ v ∈ moduleA K, yOp Tag.E6 K (jA t) c v ∈ moduleA K :=
  moduleA_le_comap fun j => by
    rw [yOp_vecA]
    exact (moduleA K).add_mem (vecA_mem j) ((moduleA K).smul_mem c (rootVec_lower_mem j t))

theorem phiA_add_smul
    {a b : RootModule Tag.E6 K} (ha : a ∈ moduleA K) (hb : b ∈ moduleA K) (c : K)
    (h : a + c • b ∈ moduleA K) :
    phiA K ⟨a + c • b, h⟩ = phiA K ⟨a, ha⟩ + c • phiA K ⟨b, hb⟩ := by
  rw [← map_smul, ← map_add]
  rfl

theorem phiA_xOp
    (t : Fin 5) (c : K) {v : RootModule Tag.E6 K} (hv : v ∈ moduleA K) :
    phiA K ⟨xOp Tag.E6 K (jA t) c v, xOp_mem_moduleA t c v hv⟩ =
      exteriorPower.map 3 (transvLin t.castSucc t.succ c) (phiA K ⟨v, hv⟩) := by
  have key : (phiA K).toLinearMap ∘ₗ (xOp Tag.E6 K (jA t) c).restrict (xOp_mem_moduleA t c) =
      exteriorPower.map 3 (transvLin t.castSucc t.succ c) ∘ₗ (phiA K).toLinearMap := by
    refine (basisA K).ext fun j => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, basisA_apply, LinearMap.restrict_apply]
    have hadj : (t.castSucc).val + 1 = (t.succ).val ∨ (t.succ).val + 1 = (t.castSucc).val :=
      Or.inl (by simp)
    rw [phiA_vecA, map_transvection_wedgeBasis hadj]
    simp only [xOp_vecA]
    rw [phiA_add_smul (vecA_mem j) (rootVec_raise_mem j t), phiA_vecA]
    rcases raise_or j t with ⟨j', hj'⟩ | hnot
    · have hcond : t.succ ∈ (eA j).val ∧ t.castSucc ∉ (eA j).val :=
        (raise_rootA j t).mp ⟨j', hj'⟩
      rw [dite_eq_left hcond]
      congr 2
      · have : (⟨rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1), rootVec_raise_mem j t⟩ :
            moduleA K) = ⟨vecA K j', vecA_mem j'⟩ := Subtype.ext
          (show rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1) = vecA K j' by rw [← hj'])
        rw [this, phiA_vecA]
        congr 1
        exact Subtype.ext (raise_subsetA j j' t hj')
    · have hcond : ¬(t.succ ∈ (eA j).val ∧ t.castSucc ∉ (eA j).val) := by
        rw [eA_val, ← raise_rootA j t]
        rintro ⟨j', hj'⟩
        exact hnot (hj' ▸ isRoot_rootA j')
      rw [dite_eq_right hcond]
      have : (⟨rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1), rootVec_raise_mem j t⟩ :
          moduleA K) = 0 := Subtype.ext
        (show rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1) = 0 from
          C2E6Std.rootVec_eq_zero_of_not hnot)
      rw [this, LinearEquiv.map_zero, smul_zero, add_zero]
  exact congrArg (fun F : moduleA K →ₗ[K] ⋀[K]^3 (Fin 6 → K) => F ⟨v, hv⟩) key

theorem phiA_yOp
    (t : Fin 5) (c : K) {v : RootModule Tag.E6 K} (hv : v ∈ moduleA K) :
    phiA K ⟨yOp Tag.E6 K (jA t) c v, yOp_mem_moduleA t c v hv⟩ =
      exteriorPower.map 3 (transvLin t.succ t.castSucc c) (phiA K ⟨v, hv⟩) := by
  have key : (phiA K).toLinearMap ∘ₗ (yOp Tag.E6 K (jA t) c).restrict (yOp_mem_moduleA t c) =
      exteriorPower.map 3 (transvLin t.succ t.castSucc c) ∘ₗ (phiA K).toLinearMap := by
    refine (basisA K).ext fun j => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, basisA_apply, LinearMap.restrict_apply]
    have hadj : (t.succ).val + 1 = (t.castSucc).val ∨ (t.castSucc).val + 1 = (t.succ).val :=
      Or.inr (by simp)
    rw [phiA_vecA, map_transvection_wedgeBasis hadj]
    simp only [yOp_vecA]
    rw [phiA_add_smul (vecA_mem j) (rootVec_lower_mem j t), phiA_vecA]
    rcases lower_or j t with ⟨j', hj'⟩ | hnot
    · have hcond : t.castSucc ∈ (eA j).val ∧ t.succ ∉ (eA j).val :=
        (lower_rootA j t).mp ⟨j', hj'⟩
      rw [dite_eq_left hcond]
      congr 2
      · have : (⟨rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1), rootVec_lower_mem j t⟩ :
            moduleA K) = ⟨vecA K j', vecA_mem j'⟩ := Subtype.ext
          (show rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1) = vecA K j' by rw [← hj'])
        rw [this, phiA_vecA]
        congr 1
        exact Subtype.ext (lower_subsetA j j' t hj')
    · have hcond : ¬(t.castSucc ∈ (eA j).val ∧ t.succ ∉ (eA j).val) := by
        rw [eA_val, ← lower_rootA j t]
        rintro ⟨j', hj'⟩
        exact hnot (hj' ▸ isRoot_rootA j')
      rw [dite_eq_right hcond]
      have : (⟨rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1), rootVec_lower_mem j t⟩ :
          moduleA K) = 0 := Subtype.ext
        (show rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1) = 0 from
          C2E6Std.rootVec_eq_zero_of_not hnot)
      rw [this, LinearEquiv.map_zero, smul_zero, add_zero]
  exact congrArg (fun F : moduleA K →ₗ[K] ⋀[K]^3 (Fin 6 → K) => F ⟨v, hv⟩) key

variable (K) in
abbrev groupA :
    Subgroup (ModGL Tag.E6 K) :=
  subsystemGroup Tag.E6 K setA

theorem mem_moduleA_of_mem_groupA
    {g : ModGL Tag.E6 K} (hg : g ∈ groupA K) :
    ∀ v ∈ moduleA K, (g : Module.End K (RootModule Tag.E6 K)) v ∈ moduleA K := by
  refine C2E6Std.mem_of_mem_subsystemGroup (fun i hi c => ?_) (fun i hi c => ?_) hg
  · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
    exact xOp_mem_moduleA t c
  · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
    exact yOp_mem_moduleA t c

variable (K) in
@[expose] def diagA : ⋀[K]^3 (Fin 6 → K) →ₗ[K] ⋀[K]^3 (Fin 6 → K) :=
  ((Pi.basisFun K (Fin 6)).exteriorPower 3).constr K fun I => wedgeBasis (compRevPC I)

variable (K) in
@[expose] def restrictEndA :
    groupA K →* Module.End K (moduleA K) where
  toFun g := ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)).restrict
    (mem_moduleA_of_mem_groupA g.2)
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem restrictEndA_apply
    (g : groupA K) (v : moduleA K) :
    ((restrictEndA K g v : moduleA K) : RootModule Tag.E6 K) =
      ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v := rfl

variable (K) in
@[expose] def psiA :
    groupA K →* (Module.End K (⋀[K]^3 (Fin 6 → K)))ˣ :=
  (Units.map (phiA K).conjRingEquiv.toMonoidHom).comp (restrictEndA K).toHomUnits

theorem psiA_apply
    (g : groupA K) (x : ⋀[K]^3 (Fin 6 → K)) :
    (psiA K g : Module.End K (⋀[K]^3 (Fin 6 → K))) x =
      phiA K (restrictEndA K g ((phiA K).symm x)) :=
  rfl

theorem psiA_eq_one_iff
    (g : groupA K) :
    psiA K g = 1 ↔
      ∀ v ∈ moduleA K, ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v = v := by
  constructor
  · intro h v hv
    have h1 := LinearMap.congr_fun (congrArg Units.val h) (phiA K ⟨v, hv⟩)
    rw [psiA_apply, LinearEquiv.symm_apply_apply, Units.val_one, Module.End.one_apply] at h1
    exact congrArg Subtype.val ((phiA K).injective h1)
  · intro h
    refine Units.ext (LinearMap.ext fun x => ?_)
    rw [psiA_apply, Units.val_one, Module.End.one_apply]
    have : restrictEndA K g ((phiA K).symm x) = (phiA K).symm x :=
      Subtype.ext (h _ ((phiA K).symm x).2)
    rw [this, LinearEquiv.apply_symm_apply]

theorem jA_mem_setA (t : Fin 5) : jA t ∈ setA := by
  fin_cases t
  exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
    Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inr (Or.inr (Or.inr (Or.inr rfl)))]

theorem xUnit_mem_groupA
    (t : Fin 5) (c : K) : xUnit Tag.E6 K (jA t) c ∈ groupA K :=
  Subgroup.subset_closure ⟨jA t, jA_mem_setA t, c, Or.inl rfl⟩

theorem yUnit_mem_groupA
    (t : Fin 5) (c : K) : yUnit Tag.E6 K (jA t) c ∈ groupA K :=
  Subgroup.subset_closure ⟨jA t, jA_mem_setA t, c, Or.inr rfl⟩

variable (K) in
abbrev upAdj (t : Fin 5) (c : K) : SpecialLinearGroup (Fin 6) K :=
  SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := t)).ne c

variable (K) in
abbrev downAdj (t : Fin 5) (c : K) : SpecialLinearGroup (Fin 6) K :=
  SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := t)).ne' c

theorem psiA_xUnit
    (t : Fin 5) (c : K) :
    psiA K ⟨xUnit Tag.E6 K (jA t) c, xUnit_mem_groupA t c⟩ = cubeHom (upAdj K t c) := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [psiA_apply, coe_cubeHom]
  have h := phiA_xOp t c ((phiA K).symm x).2
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.trans rfl

theorem psiA_yUnit
    (t : Fin 5) (c : K) :
    psiA K ⟨yUnit Tag.E6 K (jA t) c, yUnit_mem_groupA t c⟩ = cubeHom (downAdj K t c) := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [psiA_apply, coe_cubeHom]
  have h := phiA_yOp t c ((phiA K).symm x).2
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.trans rfl

variable (K) in
@[expose] def adjSet : Set (SpecialLinearGroup (Fin 6) K) :=
  {g | ∃ (t : Fin 5) (c : K), g = upAdj K t c ∨ g = downAdj K t c}

variable (K) in
@[expose] def upAdjSet : Set (SpecialLinearGroup (Fin 6) K) :=
  {g | ∃ (t : Fin 5) (c : K), g = upAdj K t c}

theorem commutator_mem_closure {G : Type*} [Group G] {S : Set G} {a b : G}
    (ha : a ∈ Subgroup.closure S) (hb : b ∈ Subgroup.closure S) :
    ⁅a, b⁆ ∈ Subgroup.closure S := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem upper_mem_closure_upAdjSet : ∀ (d : ℕ) {i j : Fin 6} (hij : i < j),
    j.val = i.val + d + 1 → ∀ c : K,
      SpecialLinearGroup.transvection hij.ne c ∈ Subgroup.closure (upAdjSet K) := by
  intro d
  induction d with
  | zero =>
    intro i j hij hd c
    have hi : i.val < 5 := by omega
    have e1 : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
    have e2 : j = Fin.succ ⟨i.val, hi⟩ := Fin.ext (by simp [hd])
    have : SpecialLinearGroup.transvection hij.ne c = upAdj K ⟨i.val, hi⟩ c := Subtype.ext (by
      rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, ← e1, ← e2])
    rw [this]
    exact Subgroup.subset_closure ⟨⟨i.val, hi⟩, c, rfl⟩
  | succ d ih =>
    intro i j hij hd c
    have hk : i.val + 1 < 6 := by omega
    set k : Fin 6 := ⟨i.val + 1, hk⟩
    have hik : i < k := Fin.lt_def.mpr (by simp [k])
    have hkj : k < j := Fin.lt_def.mpr (by simp [k]; omega)
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hik.ne hkj.ne hij.ne c 1
    rw [mul_one] at h
    rw [← h]
    refine commutator_mem_closure ?_ (ih hkj (by simp [k]; omega) 1)
    have hi : i.val < 5 := by omega
    have e1 : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
    have e2 : k = Fin.succ ⟨i.val, hi⟩ := Fin.ext (by simp [k])
    have : SpecialLinearGroup.transvection hik.ne c = upAdj K ⟨i.val, hi⟩ c := Subtype.ext (by
      simp only [SpecialLinearGroup.transvection_coe, ← e1, ← e2])
    rw [this]
    exact Subgroup.subset_closure ⟨⟨i.val, hi⟩, c, rfl⟩

theorem lower_mem_closure_adjSet : ∀ (d : ℕ) {i j : Fin 6} (hji : j < i),
    i.val = j.val + d + 1 → ∀ c : K,
      SpecialLinearGroup.transvection hji.ne' c ∈ Subgroup.closure (adjSet K) := by
  intro d
  induction d with
  | zero =>
    intro i j hji hd c
    have hj : j.val < 5 := by omega
    have e1 : j = Fin.castSucc ⟨j.val, hj⟩ := Fin.ext rfl
    have e2 : i = Fin.succ ⟨j.val, hj⟩ := Fin.ext (by simp [hd])
    have : SpecialLinearGroup.transvection hji.ne' c = downAdj K ⟨j.val, hj⟩ c := Subtype.ext (by
      rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, ← e1, ← e2])
    rw [this]
    exact Subgroup.subset_closure ⟨⟨j.val, hj⟩, c, Or.inr rfl⟩
  | succ d ih =>
    intro i j hji hd c
    have hk : i.val - 1 < 6 := by omega
    set k : Fin 6 := ⟨i.val - 1, hk⟩
    have hki : k < i := Fin.lt_def.mpr (by simp [k]; omega)
    have hjk : j < k := Fin.lt_def.mpr (by simp [k]; omega)
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hki.ne' hjk.ne' hji.ne' c 1
    rw [mul_one] at h
    rw [← h]
    refine commutator_mem_closure ?_ (ih hjk (by simp [k]; omega) 1)
    have hk5 : k.val < 5 := by simp [k]; omega
    have e1 : k = Fin.castSucc ⟨k.val, hk5⟩ := Fin.ext rfl
    have e2 : i = Fin.succ ⟨k.val, hk5⟩ := Fin.ext (by simp [k]; omega)
    have : SpecialLinearGroup.transvection hki.ne' c = downAdj K ⟨k.val, hk5⟩ c := Subtype.ext (by
      simp only [SpecialLinearGroup.transvection_coe, ← e1, ← e2])
    rw [this]
    exact Subgroup.subset_closure ⟨⟨k.val, hk5⟩, c, Or.inr rfl⟩

theorem closure_upAdjSet_le_closure_adjSet :
    Subgroup.closure (upAdjSet K) ≤ Subgroup.closure (adjSet K) :=
  Subgroup.closure_mono fun _ ⟨t, c, h⟩ => ⟨t, c, Or.inl h⟩

theorem transvection_mem_closure_adjSet {i j : Fin 6} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c ∈ Subgroup.closure (adjSet K) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact closure_upAdjSet_le_closure_adjSet
      (upper_mem_closure_upAdjSet (j.val - i.val - 1) h (by omega) c)
  · exact lower_mem_closure_adjSet (i.val - j.val - 1) h (by omega) c

theorem closure_adjSet : Subgroup.closure (adjSet K) = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 6) (K := K),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  exact transvection_mem_closure_adjSet hij c

theorem psiA_range_le :
    (psiA K).range ≤ (cubeHom (K := K)).range := by
  have htop : (⊤ : Subgroup (groupA K)) = Subgroup.closure (((↑) : groupA K → ModGL Tag.E6 K) ⁻¹'
      {g | ∃ i ∈ setA, ∃ c : K, g = xUnit Tag.E6 K i c ∨ g = yUnit Tag.E6 K i c}) :=
    Subgroup.closure_closure_coe_preimage.symm
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨i, hi, c, hg | hg⟩, rfl⟩
  · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
    have e : g = ⟨xUnit Tag.E6 K (jA t) c, xUnit_mem_groupA t c⟩ := Subtype.ext hg
    rw [e, psiA_xUnit]
    exact ⟨_, rfl⟩
  · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
    have e : g = ⟨yUnit Tag.E6 K (jA t) c, yUnit_mem_groupA t c⟩ := Subtype.ext hg
    rw [e, psiA_yUnit]
    exact ⟨_, rfl⟩

theorem cubeHom_adjSet_subset :
    cubeHom '' adjSet K ⊆ ((psiA K).range : Set _) := by
  rintro _ ⟨g, ⟨t, c, rfl | rfl⟩, rfl⟩
  · exact ⟨_, psiA_xUnit t c⟩
  · exact ⟨_, psiA_yUnit t c⟩

theorem range_psiA :
    (psiA K).range = (cubeHom (K := K)).range := by
  refine le_antisymm psiA_range_le ?_
  rw [MonoidHom.range_eq_map, ← closure_adjSet, MonoidHom.map_closure, Subgroup.closure_le]
  exact cubeHom_adjSet_subset

end CFSG.LieType.Chevalley.E6A5Cube
