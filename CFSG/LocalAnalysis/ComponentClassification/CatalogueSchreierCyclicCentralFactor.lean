module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCyclicCentralFactorOuter
public import CFSG.LocalAnalysis.ComponentClassification.CenterlessCommutingFamily

public section

namespace CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor

open OuterAutomorphisms

variable {H : Type*} [Group H]

theorem central_factor_centralizes (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) : Z ≤ Subgroup.centralizer (L : Set H) := by
  intro member hmember
  apply Subgroup.mem_centralizer_iff.mpr
  intro other _
  exact Subgroup.mem_center_iff.mp (hcentral hmember) other

theorem internal_factor_normal (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcover : L ⊔ Z = ⊤) : L.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hcover]
  exact sup_le Subgroup.le_normalizer
    ((central_factor_centralizes L Z hcentral).trans (Subgroup.centralizer_le_normalizer _))

theorem internal_factors_disjoint (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥) :
    Disjoint L Z :=
  CenterlessCommutingFamily.disjoint_of_centralizes L Z hcenter
    (central_factor_centralizes L Z hcentral)

@[expose] def internalMultiplication (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) : L × Z →* H :=
  L.subtype.noncommCoprod Z.subtype
    (fun left right => Subgroup.mem_center_iff.mp (hcentral right.property) left)

theorem internalMultiplication_injective (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥) :
    Function.Injective (internalMultiplication L Z hcentral) :=
  Subgroup.mul_injective_of_disjoint (internal_factors_disjoint L Z hcentral hcenter)

theorem internalMultiplication_surjective (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcover : L ⊔ Z = ⊤) :
    Function.Surjective (internalMultiplication L Z hcentral) := by
  let : L.Normal := internal_factor_normal L Z hcentral hcover
  intro member
  have hmember : member ∈ L ⊔ Z := hcover.symm ▸ Subgroup.mem_top member
  obtain ⟨left, hleft, right, hright, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hmember
  exact ⟨(⟨left, hleft⟩, ⟨right, hright⟩), heq⟩

@[expose] noncomputable def internalEquivalence (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) : L × Z ≃* H :=
  MulEquiv.ofBijective (internalMultiplication L Z hcentral)
    ⟨internalMultiplication_injective L Z hcentral hcenter,
      internalMultiplication_surjective L Z hcentral hcover⟩

theorem internalEquivalence_apply (L Z : Subgroup H)
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) (left : L) (right : Z) :
    internalEquivalence L Z hcentral hcenter hcover (left, right) = left.val * right.val := rfl

@[expose] noncomputable def internalAutomorphismEquivalence (L Z : Subgroup H)
    [Group.IsPerfect L] [IsCyclic Z]
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) : MulAut H ≃* MulAut L × MulAut Z :=
  (MulAut.congr (internalEquivalence L Z hcentral hcenter hcover).symm).trans
    (automorphismEquivalence hcenter)

theorem internalAutomorphismEquivalence_left (L Z : Subgroup H)
    [Group.IsPerfect L] [IsCyclic Z]
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) (automorphism : MulAut H) (member : L) :
    ((internalAutomorphismEquivalence L Z hcentral hcenter hcover automorphism).1 member).val =
      automorphism member.val := by
  let productEquivalence := internalEquivalence L Z hcentral hcenter hcover
  let productAutomorphism := MulAut.congr productEquivalence.symm automorphism
  change ((automorphismEquivalence hcenter productAutomorphism).1 member).val = _
  rw [automorphismEquivalence_apply]
  change (productAutomorphism (member, 1)).1.val = _
  have hpair := automorphism_inl_second productAutomorphism member
  have hvalue := productEquivalence.apply_symm_apply (automorphism (productEquivalence (member, 1)))
  change productEquivalence (productAutomorphism (member, 1)) =
    automorphism (productEquivalence (member, 1)) at hvalue
  have hdecomposition : productAutomorphism (member, 1) =
      ((productAutomorphism (member, 1)).1, 1) := Prod.ext rfl hpair
  rw [hdecomposition] at hvalue
  simpa only [productEquivalence, internalEquivalence_apply, OneMemClass.coe_one,
    mul_one] using hvalue

theorem internalAutomorphismEquivalence_right (L Z : Subgroup H)
    [Group.IsPerfect L] [IsCyclic Z]
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) (automorphism : MulAut H) (member : Z) :
    ((internalAutomorphismEquivalence L Z hcentral hcenter hcover automorphism).2 member).val =
      automorphism member.val := by
  let productEquivalence := internalEquivalence L Z hcentral hcenter hcover
  let productAutomorphism := MulAut.congr productEquivalence.symm automorphism
  change ((automorphismEquivalence hcenter productAutomorphism).2 member).val = _
  rw [automorphismEquivalence_apply]
  change (productAutomorphism (1, member)).2.val = _
  have hpair := automorphism_inr_first hcenter productAutomorphism member
  have hvalue := productEquivalence.apply_symm_apply (automorphism (productEquivalence (1, member)))
  change productEquivalence (productAutomorphism (1, member)) =
    automorphism (productEquivalence (1, member)) at hvalue
  have hdecomposition : productAutomorphism (1, member) =
      (1, (productAutomorphism (1, member)).2) := Prod.ext hpair rfl
  rw [hdecomposition] at hvalue
  simpa only [productEquivalence, internalEquivalence_apply, OneMemClass.coe_one,
    one_mul] using hvalue

theorem internal_factors_characteristic (L Z : Subgroup H)
    [Group.IsPerfect L] [IsCyclic Z]
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) : L.Characteristic ∧ Z.Characteristic := by
  constructor
  · apply Subgroup.characteristic_iff_map_le.mpr
    intro automorphism
    rintro _ ⟨member, hmember, rfl⟩
    have hvalue := internalAutomorphismEquivalence_left L Z hcentral hcenter hcover
      automorphism (⟨member, hmember⟩ : L)
    change automorphism member ∈ L
    change _ = automorphism member at hvalue
    rw [← hvalue]
    exact ((internalAutomorphismEquivalence L Z hcentral hcenter hcover
      automorphism).1 (⟨member, hmember⟩ : L)).property
  · apply Subgroup.characteristic_iff_map_le.mpr
    intro automorphism
    rintro _ ⟨member, hmember, rfl⟩
    have hvalue := internalAutomorphismEquivalence_right L Z hcentral hcenter hcover
      automorphism (⟨member, hmember⟩ : Z)
    change automorphism member ∈ Z
    change _ = automorphism member at hvalue
    rw [← hvalue]
    exact ((internalAutomorphismEquivalence L Z hcentral hcenter hcover
      automorphism).2 (⟨member, hmember⟩ : Z)).property

@[expose] noncomputable def internalOuterEquivalence (L Z : Subgroup H)
    [Group.IsPerfect L] [IsCyclic Z]
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) : Outer H ≃* Outer L × MulAut Z :=
  (equivalence (internalEquivalence L Z hcentral hcenter hcover).symm).trans
    (outerEquivalence hcenter)

theorem internal_outer_solvable (L Z : Subgroup H) [Group.IsPerfect L] [IsCyclic Z]
    (hcentral : Z ≤ Subgroup.center H) (hcenter : Subgroup.center L = ⊥)
    (hcover : L ⊔ Z = ⊤) [Group.IsSolvable (Outer L)] :
    Group.IsSolvable (Outer H) := by
  let : Group.IsSolvable (Outer (L × Z)) := outer_solvable_of_cyclic hcenter
  exact solvable_of_equiv (internalEquivalence L Z hcentral hcenter hcover)

end CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor
