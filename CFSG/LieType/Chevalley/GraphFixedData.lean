module

public import CFSG.LieType.Chevalley.TwistMapFixed
public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.WeylInversion
public import CFSG.LieType.Chevalley.FoldedWeylData

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] def graphFixedBorel
    : Subgroup (ModGL t.tag K) :=
  borelGroup t.tag K ⊓ twistedFixedGroup t K σ

@[expose] def graphFixedTorus
    : Subgroup (ModGL t.tag K) :=
  torusGroup t.tag K ⊓ twistedFixedGroup t K σ

@[expose] def graphFixedMonomial
    : Subgroup (ModGL t.tag K) :=
  monomialSubgroup t.tag K ⊓ twistedFixedGroup t K σ

@[expose] def graphFixedPosUnipotent
    : Subgroup (ModGL t.tag K) :=
  posUnipotent t.tag K ⊓ twistedFixedGroup t K σ

@[expose] def graphFixedNegUnipotent
    : Subgroup (ModGL t.tag K) :=
  negUnipotent t.tag K ⊓ twistedFixedGroup t K σ

@[expose] def graphFixedRootGroup
    : Subgroup (ModGL t.tag K) :=
  graphFixedPosUnipotent t K σ ⊔ graphFixedNegUnipotent t K σ

@[expose] def graphFixedInversionUnipotent
    (w : WeylGroup t.tag) : Subgroup (ModGL t.tag K) :=
  rootSpan t.tag K (inversionSet w) ⊓ twistedFixedGroup t K σ

theorem mem_twistedFixedGroup_iff_twistHom {g : ModGL t.tag K} :
    g ∈ twistedFixedGroup t K σ ↔ g ∈ adjointGroup t.tag K ∧ twistHom t K σ g = g :=
  Iff.rfl

theorem graphFixedBorel_le
    : graphFixedBorel t K σ ≤ twistedFixedGroup t K σ :=
  inf_le_right

theorem graphFixedTorus_le
    : graphFixedTorus t K σ ≤ twistedFixedGroup t K σ :=
  inf_le_right

theorem graphFixedMonomial_le
    : graphFixedMonomial t K σ ≤ twistedFixedGroup t K σ :=
  inf_le_right

theorem graphFixedPosUnipotent_le
    : graphFixedPosUnipotent t K σ ≤ twistedFixedGroup t K σ :=
  inf_le_right

theorem graphFixedNegUnipotent_le
    : graphFixedNegUnipotent t K σ ≤ twistedFixedGroup t K σ :=
  inf_le_right

theorem graphFixedRootGroup_le
    : graphFixedRootGroup t K σ ≤ twistedFixedGroup t K σ :=
  sup_le (graphFixedPosUnipotent_le t K σ) (graphFixedNegUnipotent_le t K σ)

theorem graphFixedInversionUnipotent_le
    (w : WeylGroup t.tag) :
    graphFixedInversionUnipotent t K σ w ≤ twistedFixedGroup t K σ :=
  inf_le_right

theorem graphFixedPosUnipotent_le_graphFixedRootGroup :
    graphFixedPosUnipotent t K σ ≤ graphFixedRootGroup t K σ :=
  le_sup_left

theorem graphFixedNegUnipotent_le_graphFixedRootGroup :
    graphFixedNegUnipotent t K σ ≤ graphFixedRootGroup t K σ :=
  le_sup_right

@[expose] def graphFixedRootBorel
    : Subgroup (ModGL t.tag K) :=
  graphFixedBorel t K σ ⊓ graphFixedRootGroup t K σ

@[expose] def graphFixedRootTorus
    : Subgroup (ModGL t.tag K) :=
  graphFixedTorus t K σ ⊓ graphFixedRootGroup t K σ

@[expose] def graphFixedRootMonomial
    : Subgroup (ModGL t.tag K) :=
  graphFixedMonomial t K σ ⊓ graphFixedRootGroup t K σ

theorem graphFixedRootBorel_le
    : graphFixedRootBorel t K σ ≤ graphFixedRootGroup t K σ :=
  inf_le_right

theorem graphFixedRootTorus_le
    : graphFixedRootTorus t K σ ≤ graphFixedRootGroup t K σ :=
  inf_le_right

theorem graphFixedRootMonomial_le
    : graphFixedRootMonomial t K σ ≤ graphFixedRootGroup t K σ :=
  inf_le_right

section Order

variable {τ : Tag} {R : Type} [CommRing R]

theorem entrywise_entrywise (σ σ' : R →+* R) (A : Module.End R (RootModule τ R)) :
    entrywise σ (entrywise σ' A) = entrywise (σ.comp σ') A := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, entrywise_single, entrywise_single, Finsupp.mapRange_mapRange]
  rfl

theorem entrywise_id (A : Module.End R (RootModule τ R)) : entrywise (RingHom.id R) A = A := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single]
  exact Finsupp.mapRange_id _

end Order

variable {t K}

theorem entrywise_diagramMap :
    entrywise σ (diagramMap t K : Module.End K (RootModule t.tag K)) = diagramMap t K := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single]
  simp [diagramMap]

theorem units_map_entrywiseHom_diagramMap :
    Units.map (entrywiseHom σ) (diagramMap t K) = diagramMap t K :=
  Units.ext (entrywise_diagramMap σ)

theorem units_map_entrywiseHom_comp (σ' : K →+* K) (g : ModGL t.tag K) :
    Units.map (entrywiseHom σ) (Units.map (entrywiseHom σ') g) =
      Units.map (entrywiseHom (σ.comp σ')) g := by
  ext1
  simp only [Units.coe_map]
  exact entrywise_entrywise σ σ' _

theorem twistHom_apply (g : ModGL t.tag K) :
    twistHom t K σ g = diagramMap t K * Units.map (entrywiseHom σ) g * (diagramMap t K)⁻¹ :=
  rfl

variable (t K)

theorem diagramMap_pow_hVec (k : ℕ) (i : Fin t.tag.rank) :
    ((diagramMap t K ^ k : ModGL t.tag K) : Module.End K (RootModule t.tag K)) (hVec t.tag K i) =
      hVec t.tag K ((t.perm ^ k) i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih, diagramMap_hVec, pow_succ',
      Equiv.Perm.mul_apply]

theorem diagramMap_pow_rootVec
    (k : ℕ) (β : Fin t.tag.rank → ℤ) :
    ((diagramMap t K ^ k : ModGL t.tag K) : Module.End K (RootModule t.tag K))
        (rootVec t.tag K β) = rootVec t.tag K (permLattice (t.perm ^ k) β) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih, diagramMap_apply_rootVec, pow_succ']
    rfl

theorem diagramMap_pow_order :
    diagramMap t K ^ t.order = 1 := by
  refine Units.ext (rootModule_end_ext (fun j => ?_) (fun α _ => ?_))
  · rw [diagramMap_pow_hVec, t.perm_pow_order]
    rfl
  · rw [diagramMap_pow_rootVec, t.perm_pow_order]
    rfl

variable {t K}

theorem twistHom_iterate (k : ℕ) (g : ModGL t.tag K) :
    (twistHom t K σ)^[k] g =
      diagramMap t K ^ k * Units.map (entrywiseHom (σ ^ k)) g * (diagramMap t K ^ k)⁻¹ := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, pow_zero, inv_one, mul_one, one_mul]
    exact (Units.ext (entrywise_id (g : Module.End K (RootModule t.tag K)))).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, twistHom_apply, map_mul, map_mul, map_inv, map_pow,
      units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp, pow_succ' σ,
      RingHom.mul_def, pow_succ' (diagramMap t K)]
    group

theorem twistHom_iterate_order
    (g : ModGL t.tag K) :
    (twistHom t K σ)^[t.order] g = Units.map (entrywiseHom (σ ^ t.order)) g := by
  rw [twistHom_iterate, diagramMap_pow_order, inv_one, one_mul, mul_one]

theorem twistHom_iterate_order_of_pow_eq_one
    (hσ : σ ^ t.order = 1) (g : ModGL t.tag K) :
    (twistHom t K σ)^[t.order] g = g := by
  rw [twistHom_iterate_order, hσ]
  exact Units.ext (entrywise_id (g : Module.End K (RootModule t.tag K)))

end CFSG.LieType.Chevalley
