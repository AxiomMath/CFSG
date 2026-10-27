module

public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6ExteriorCube
public import CFSG.LieType.Chevalley.C2E6StandardFixedData

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.ExteriorCube exteriorPower Set

@[expose] def i6 (i : Fin 6) : Fin Tag.E6.rank := i

@[expose] def jA : Fin 5 → Fin Tag.E6.rank := (![0, 2, 3, 4, 5] : Fin 5 → Fin 6)

@[expose] def rootWeight (i : Fin Tag.E6.rank) (α : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ j, Tag.E6.cartan i j * α j

@[expose] def rootA : Fin 20 → Fin Tag.E6.rank → ℤ := (
  ![![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0],
    ![0, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0],
    ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 0], ![1, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1]] :
    Fin 20 → Fin 6 → ℤ)

@[expose] def subsetA : Fin 20 → Finset (Fin 6) :=
  ![{3, 4, 5}, {2, 4, 5}, {2, 3, 5}, {2, 3, 4}, {1, 4, 5}, {1, 3, 5}, {1, 3, 4},
    {1, 2, 5}, {1, 2, 4}, {1, 2, 3}, {0, 4, 5}, {0, 3, 5}, {0, 3, 4}, {0, 2, 5},
    {0, 2, 4}, {0, 2, 3}, {0, 1, 5}, {0, 1, 4}, {0, 1, 3}, {0, 1, 2}]

@[expose] def subsetPattern (I : Finset (Fin 6)) (t : Fin 5) : ℤ :=
  (if t.castSucc ∈ I then 1 else 0) - (if t.succ ∈ I then 1 else 0)

@[expose] def compRev (I : Finset (Fin 6)) : Finset (Fin 6) := Finset.univ \ I.image Fin.rev

abbrev rhoL (α : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ := permLattice TwistTag.E6.perm α

theorem exists_e6Root_eq_rootA : ∀ j : Fin 20, ∃ k : Fin 72, e6Root k = rootA j := by
  decide +kernel

theorem rootA_one : ∀ j : Fin 20, rootA j (i6 1) = 1 := by decide

theorem exists_rootA_eq_e6Root : ∀ k : Fin 72, e6Root k (i6 1) = 1 →
    ∃ j : Fin 20, rootA j = e6Root k := by
  decide +kernel

theorem rootA_injective : Function.Injective rootA := by
  intro j j' h
  revert j j'
  decide

theorem card_subsetA : ∀ j, (subsetA j).card = 3 := by decide

theorem subsetA_injective : Function.Injective subsetA := by
  intro j j' h
  revert j j'
  decide

theorem exists_subsetA_eq : ∀ I : Finset (Fin 6), I.card = 3 → ∃ j, subsetA j = I := by
  decide

theorem weight_rootA : ∀ (j : Fin 20) (t : Fin 5),
    rootWeight (jA t) (rootA j) = subsetPattern (subsetA j) t := by
  decide

theorem eq_of_weight : ∀ j j' : Fin 20,
    (∀ t, rootWeight (jA t) (rootA j) = subsetPattern (subsetA j') t) → j' = j := by
  decide

theorem raise_rootA : ∀ (j : Fin 20) (t : Fin 5),
    ((∃ j', rootA j' = rootA j + Pi.single (jA t) 1) ↔
      (t.succ ∈ subsetA j ∧ t.castSucc ∉ subsetA j)) := by
  decide

theorem raise_subsetA : ∀ (j j' : Fin 20) (t : Fin 5),
    rootA j' = rootA j + Pi.single (jA t) 1 →
      subsetA j' = insert t.castSucc ((subsetA j).erase t.succ) := by
  decide

theorem lower_rootA : ∀ (j : Fin 20) (t : Fin 5),
    ((∃ j', rootA j' = rootA j - Pi.single (jA t) 1) ↔
      (t.castSucc ∈ subsetA j ∧ t.succ ∉ subsetA j)) := by
  decide

theorem lower_subsetA : ∀ (j j' : Fin 20) (t : Fin 5),
    rootA j' = rootA j - Pi.single (jA t) 1 →
      subsetA j' = insert t.succ ((subsetA j).erase t.castSucc) := by
  decide

theorem rootA_ne_single : ∀ (j : Fin 20) (t : Fin 5),
    rootA j ≠ Pi.single (jA t) 1 ∧ rootA j ≠ -Pi.single (jA t) 1 := by
  decide

theorem diag_rootA : ∀ j : Fin 20, ∃ j', rootA j' = rhoL (rootA j) ∧
    subsetA j' = compRev (subsetA j) := by
  decide

theorem isRoot_rootA (j : Fin 20) : IsRoot Tag.E6 (rootA j) := by
  obtain ⟨k, hk⟩ := exists_e6Root_eq_rootA j
  rw [← hk]
  exact isRoot_e6Root k

theorem exists_rootA_eq
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h1 : α (1 : Fin 6) = 1) : ∃ j, rootA j = α := by
  obtain ⟨k, rfl⟩ := exists_e6Root_eq hα
  exact exists_rootA_eq_e6Root k h1

abbrev vecA (j : Fin 20) : RootModule Tag.E6 K := rootVec Tag.E6 K (rootA j)

theorem moduleA_eq_span
    : moduleA = Submodule.span K (Set.range vecA) := by
  rw [moduleA]
  congr 1
  ext v
  constructor
  · rintro ⟨α, hα, h1, rfl⟩
    obtain ⟨j, rfl⟩ := exists_rootA_eq hα h1
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨rootA j, isRoot_rootA j, rootA_one j, rfl⟩

theorem vecA_mem (j : Fin 20) : vecA j ∈ moduleA := by
  rw [moduleA_eq_span]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem linearIndependent_vecA : LinearIndependent K vecA := by
  have h := (Finsupp.basisSingleOne (R := K) (ι := Label Tag.E6)).linearIndependent.comp
    (fun j => (Sum.inr ⟨rootA j, isRoot_rootA j⟩ : Label Tag.E6))
    (fun j j' h => rootA_injective (by simpa using h))
  convert h using 1
  funext j
  simp [vecA, rootVec_eq_single (isRoot_rootA j)]

@[expose] def basisA : Module.Basis (Fin 20) K moduleA :=
  (Module.Basis.span linearIndependent_vecA).map (LinearEquiv.ofEq _ _ moduleA_eq_span.symm)

theorem basisA_apply
    (j : Fin 20) : basisA j = ⟨vecA j, vecA_mem j⟩ := by
  apply Subtype.ext
  simp [basisA, Module.Basis.span_apply]

@[expose] def eA : Fin 20 ≃ powersetCard (Fin 6) 3 :=
  Equiv.ofBijective (fun j => ⟨subsetA j, card_subsetA j⟩)
    ⟨fun j j' h => subsetA_injective (congrArg Subtype.val h), fun I => by
      obtain ⟨j, hj⟩ := exists_subsetA_eq I.val I.prop
      exact ⟨j, Subtype.ext hj⟩⟩

theorem eA_val (j : Fin 20) : (eA j).val = subsetA j := rfl

@[expose] def phiA : moduleA ≃ₗ[K] ⋀[K]^3 (Fin 6 → K) :=
  basisA.equiv ((Pi.basisFun K (Fin 6)).exteriorPower 3) eA

theorem phiA_vecA
    (j : Fin 20) : phiA ⟨vecA j, vecA_mem j⟩ = wedgeBasis (eA j) := by
  rw [← basisA_apply, phiA, Module.Basis.equiv_apply, wedgeBasis_eq_basis]

theorem phiA_rootVec
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (h1 : α (1 : Fin 6) = 1)
    (hmem : rootVec Tag.E6 K α ∈ moduleA) (I : powersetCard (Fin 6) 3)
    (hI : ∀ t : Fin 5, rootWeight (jA t) α = subsetPattern I.val t) :
    phiA ⟨rootVec Tag.E6 K α, hmem⟩ = wedgeBasis I := by
  obtain ⟨j, rfl⟩ := exists_rootA_eq hα h1
  obtain ⟨j', rfl⟩ := eA.surjective I
  rw [eq_of_weight j j' hI]
  exact phiA_vecA j

theorem existsUnique_subset
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h1 : α (1 : Fin 6) = 1) :
    ∃! I : powersetCard (Fin 6) 3, ∀ t : Fin 5, rootWeight (jA t) α = subsetPattern I.val t := by
  obtain ⟨j, rfl⟩ := exists_rootA_eq hα h1
  refine ⟨eA j, weight_rootA j, fun I hI => ?_⟩
  obtain ⟨j', rfl⟩ := eA.surjective I
  rw [eq_of_weight j j' hI]

theorem jA_ne_one (t : Fin 5) : jA t ≠ i6 1 := by
  revert t
  decide

theorem raise_or (j : Fin 20) (t : Fin 5) :
    (∃ j', rootA j' = rootA j + Pi.single (jA t) 1) ∨
      ¬IsRoot Tag.E6 (rootA j + Pi.single (jA t) 1) := by
  by_cases h : IsRoot Tag.E6 (rootA j + Pi.single (jA t) 1)
  · refine Or.inl (exists_rootA_eq h ?_)
    have h := rootA_one j
    have hne := jA_ne_one t
    show (rootA j + Pi.single (jA t) 1 : Fin Tag.E6.rank → ℤ) (i6 1) = 1
    rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hne), add_zero]
    exact h
  · exact Or.inr h

theorem lower_or (j : Fin 20) (t : Fin 5) :
    (∃ j', rootA j' = rootA j - Pi.single (jA t) 1) ∨
      ¬IsRoot Tag.E6 (rootA j - Pi.single (jA t) 1) := by
  by_cases h : IsRoot Tag.E6 (rootA j - Pi.single (jA t) 1)
  · refine Or.inl (exists_rootA_eq h ?_)
    have h := rootA_one j
    have hne := jA_ne_one t
    show (rootA j - Pi.single (jA t) 1 : Fin Tag.E6.rank → ℤ) (i6 1) = 1
    rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hne), sub_zero]
    exact h
  · exact Or.inr h

theorem xOp_vecA
    (j : Fin 20) (t : Fin 5) (c : K) :
    xOp Tag.E6 K (jA t) c (vecA j) =
      vecA j + c • rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1) :=
  xOp_rootVec_E6 (jA t) c (isRoot_rootA j) (rootA_ne_single j t).1 (rootA_ne_single j t).2

theorem yOp_vecA
    (j : Fin 20) (t : Fin 5) (c : K) :
    yOp Tag.E6 K (jA t) c (vecA j) =
      vecA j + c • rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1) :=
  yOp_rootVec_E6 (jA t) c (isRoot_rootA j) (rootA_ne_single j t).1 (rootA_ne_single j t).2

theorem rootVec_raise_mem (j : Fin 20) (t : Fin 5) :
    rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1) ∈ moduleA := by
  rcases raise_or j t with ⟨j', hj'⟩ | h
  · rw [← hj']
    exact vecA_mem j'
  · rw [rootVec_eq_zero_of_not h]
    exact Submodule.zero_mem _

theorem rootVec_lower_mem (j : Fin 20) (t : Fin 5) :
    rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1) ∈ moduleA := by
  rcases lower_or j t with ⟨j', hj'⟩ | h
  · rw [← hj']
    exact vecA_mem j'
  · rw [rootVec_eq_zero_of_not h]
    exact Submodule.zero_mem _

theorem moduleA_le_comap {f : Module.End K (RootModule Tag.E6 K)}
    (hf : ∀ j, f (vecA j) ∈ moduleA) : ∀ v ∈ moduleA, f v ∈ moduleA := by
  intro v hv
  have : moduleA ≤ moduleA.comap f := by
    conv_lhs => rw [moduleA_eq_span]
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hf j
  exact this hv

theorem xOp_mem_moduleA
    (t : Fin 5) (c : K) :
    ∀ v ∈ moduleA, xOp Tag.E6 K (jA t) c v ∈ moduleA :=
  moduleA_le_comap fun j => by
    rw [xOp_vecA]
    exact moduleA.add_mem (vecA_mem j) (moduleA.smul_mem c (rootVec_raise_mem j t))

theorem yOp_mem_moduleA
    (t : Fin 5) (c : K) :
    ∀ v ∈ moduleA, yOp Tag.E6 K (jA t) c v ∈ moduleA :=
  moduleA_le_comap fun j => by
    rw [yOp_vecA]
    exact moduleA.add_mem (vecA_mem j) (moduleA.smul_mem c (rootVec_lower_mem j t))

theorem phiA_add_smul
    {a b : RootModule Tag.E6 K} (ha : a ∈ moduleA) (hb : b ∈ moduleA) (c : K)
    (h : a + c • b ∈ moduleA) :
    phiA ⟨a + c • b, h⟩ = phiA ⟨a, ha⟩ + c • phiA ⟨b, hb⟩ := by
  rw [← map_smul, ← map_add]
  rfl

theorem phiA_zero_mem
    (h : (0 : RootModule Tag.E6 K) ∈ moduleA) : phiA ⟨0, h⟩ = 0 :=
  map_zero phiA

theorem phiA_xOp
    (t : Fin 5) (c : K) {v : RootModule Tag.E6 K} (hv : v ∈ moduleA) :
    phiA ⟨xOp Tag.E6 K (jA t) c v, xOp_mem_moduleA t c v hv⟩ =
      exteriorPower.map 3 (transvLin t.castSucc t.succ c) (phiA ⟨v, hv⟩) := by
  have key : phiA.toLinearMap ∘ₗ (xOp Tag.E6 K (jA t) c).restrict (xOp_mem_moduleA t c) =
      exteriorPower.map 3 (transvLin t.castSucc t.succ c) ∘ₗ phiA.toLinearMap := by
    refine basisA.ext fun j => ?_
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
            moduleA) = ⟨vecA j', vecA_mem j'⟩ := Subtype.ext
          (show rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1) = vecA j' by rw [← hj'])
        rw [this, phiA_vecA]
        congr 1
        exact Subtype.ext (raise_subsetA j j' t hj')
    · have hcond : ¬(t.succ ∈ (eA j).val ∧ t.castSucc ∉ (eA j).val) := by
        rw [eA_val, ← raise_rootA j t]
        rintro ⟨j', hj'⟩
        exact hnot (hj' ▸ isRoot_rootA j')
      rw [dite_eq_right hcond]
      have : (⟨rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1), rootVec_raise_mem j t⟩ :
          moduleA) = 0 := Subtype.ext
        (show rootVec Tag.E6 K (rootA j + Pi.single (jA t) 1) = 0 from rootVec_eq_zero_of_not hnot)
      rw [this, map_zero, smul_zero, add_zero]
  exact congrArg (fun F : moduleA →ₗ[K] ⋀[K]^3 (Fin 6 → K) => F ⟨v, hv⟩) key

theorem phiA_yOp
    (t : Fin 5) (c : K) {v : RootModule Tag.E6 K} (hv : v ∈ moduleA) :
    phiA ⟨yOp Tag.E6 K (jA t) c v, yOp_mem_moduleA t c v hv⟩ =
      exteriorPower.map 3 (transvLin t.succ t.castSucc c) (phiA ⟨v, hv⟩) := by
  have key : phiA.toLinearMap ∘ₗ (yOp Tag.E6 K (jA t) c).restrict (yOp_mem_moduleA t c) =
      exteriorPower.map 3 (transvLin t.succ t.castSucc c) ∘ₗ phiA.toLinearMap := by
    refine basisA.ext fun j => ?_
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
            moduleA) = ⟨vecA j', vecA_mem j'⟩ := Subtype.ext
          (show rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1) = vecA j' by rw [← hj'])
        rw [this, phiA_vecA]
        congr 1
        exact Subtype.ext (lower_subsetA j j' t hj')
    · have hcond : ¬(t.castSucc ∈ (eA j).val ∧ t.succ ∉ (eA j).val) := by
        rw [eA_val, ← lower_rootA j t]
        rintro ⟨j', hj'⟩
        exact hnot (hj' ▸ isRoot_rootA j')
      rw [dite_eq_right hcond]
      have : (⟨rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1), rootVec_lower_mem j t⟩ :
          moduleA) = 0 := Subtype.ext
        (show rootVec Tag.E6 K (rootA j - Pi.single (jA t) 1) = 0 from rootVec_eq_zero_of_not hnot)
      rw [this, map_zero, smul_zero, add_zero]
  exact congrArg (fun F : moduleA →ₗ[K] ⋀[K]^3 (Fin 6 → K) => F ⟨v, hv⟩) key

theorem exists_jA_of_mem_setA {i : Fin Tag.E6.rank} (hi : i ∈ setA) : ∃ t, jA t = i := by
  simp only [setA] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

theorem mem_moduleA_of_mem_groupA
    {g : ModGL Tag.E6 K} (hg : g ∈ groupA) :
    ∀ v ∈ moduleA, (g : Module.End K (RootModule Tag.E6 K)) v ∈ moduleA := by
  refine mem_of_mem_subsystemGroup (fun i hi c => ?_) (fun i hi c => ?_) hg
  · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
    exact xOp_mem_moduleA t c
  · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
    exact yOp_mem_moduleA t c

theorem card_compRev {I : Finset (Fin 6)} (hI : I.card = 3) : (compRev I).card = 3 := by
  rw [compRev, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_image_of_injective _ Fin.rev_injective, hI, Finset.card_univ, Fintype.card_fin]

@[expose] def compRevPC (I : powersetCard (Fin 6) 3) : powersetCard (Fin 6) 3 :=
  ⟨compRev I.val, card_compRev I.prop⟩

@[expose] def diagA : ⋀[K]^3 (Fin 6 → K) →ₗ[K] ⋀[K]^3 (Fin 6 → K) :=
  ((Pi.basisFun K (Fin 6)).exteriorPower 3).constr K fun I => wedgeBasis (compRevPC I)

theorem diagA_wedgeBasis (I : powersetCard (Fin 6) 3) :
    diagA (wedgeBasis I) = wedgeBasis (compRevPC I) := by
  rw [diagA, wedgeBasis_eq_basis I, Module.Basis.constr_basis]

abbrev diagE6 : Module.End K (RootModule Tag.E6 K) := (diagramMap TwistTag.E6 K).val

theorem diagramMap_vecA (j : Fin 20) :
    diagE6 (vecA j) =
      rootVec Tag.E6 K (rhoL (rootA j)) :=
  diagramMap_rootVec TwistTag.E6 K (rootA j) (isRoot_rootA j)

theorem diagramMap_mem_moduleA :
    ∀ v ∈ moduleA, diagE6 v ∈ moduleA :=
  moduleA_le_comap fun j => by
    rw [diagramMap_vecA]
    obtain ⟨j', hj', -⟩ := diag_rootA j
    rw [← hj']
    exact vecA_mem j'

theorem phiA_diagramMap {v : RootModule Tag.E6 K} (hv : v ∈ moduleA) :
    phiA ⟨diagE6 v,
      diagramMap_mem_moduleA v hv⟩ = diagA (phiA ⟨v, hv⟩) := by
  have key : phiA.toLinearMap ∘ₗ
      diagE6.restrict
        diagramMap_mem_moduleA = diagA ∘ₗ phiA.toLinearMap := by
    refine basisA.ext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, basisA_apply, LinearMap.restrict_apply]
    obtain ⟨j', hj', hsub⟩ := diag_rootA j
    have : (⟨diagE6 (vecA j), diagramMap_mem_moduleA _ (vecA_mem j)⟩ : moduleA) =
        ⟨vecA j', vecA_mem j'⟩ :=
      Subtype.ext (show diagE6 (vecA j) = vecA j' by rw [diagramMap_vecA, ← hj'])
    refine (congrArg phiA this).trans ?_
    rw [LinearEquiv.coe_coe, phiA_vecA, phiA_vecA, diagA_wedgeBasis]
    congr 1
    exact Subtype.ext hsub
  exact congrArg (fun F : moduleA →ₗ[K] ⋀[K]^3 (Fin 6 → K) => F ⟨v, hv⟩) key

end CFSG.LieType.Chevalley.C2E6Std
