module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra

public noncomputable section

open scoped commutatorElement

namespace CFSG.GroupTheory.FixedCentralQuotientFamily

open CFSG.ComponentClassification
open CatalogueBFixedCentralQuotient

variable {X : Type*} [Group X] {ι : Type*}
  (Z : Subgroup X) [Z.Normal] (ψ : ι → MulAut X)
  (hinv : ∀ i, Z.map (ψ i).toMonoidHom = Z)

@[expose] def commonFixed : Subgroup X :=
  ⨅ i, FixedCommutingProduct.fixedSubgroup (ψ i)

@[expose] def quotientFixed : Subgroup (X ⧸ Z) :=
  ⨅ i, FixedCommutingProduct.fixedSubgroup (onQuotient Z (ψ i) (hinv i))

@[expose] def fixedPreimage : Subgroup X :=
  (quotientFixed Z ψ hinv).comap (QuotientGroup.mk' Z)

theorem fixedPreimage_le (i : ι) :
    fixedPreimage Z ψ hinv ≤ CatalogueBFixedCentralQuotient.fixedPreimage Z (ψ i) (hinv i) := by
  intro x hx
  exact Subgroup.mem_iInf.mp hx i

theorem commonFixed_le : commonFixed ψ ≤ fixedPreimage Z ψ hinv := by
  intro x hx
  apply Subgroup.mem_iInf.mpr
  intro i
  exact fixed_le_fixedPreimage Z (ψ i) (hinv i) (Subgroup.mem_iInf.mp hx i)

@[expose] def displacement (hZ : Z ≤ Subgroup.center X) :
    fixedPreimage Z ψ hinv →* (ι → Z) :=
  MonoidHom.pi fun i =>
    (CatalogueBFixedCentralQuotient.displacement Z (ψ i) (hinv i) hZ).comp
      (Subgroup.inclusion (fixedPreimage_le Z ψ hinv i))

theorem displacement_eq_one_iff (hZ : Z ≤ Subgroup.center X)
    (x : fixedPreimage Z ψ hinv) :
    displacement Z ψ hinv hZ x = 1 ↔ ∀ i, ψ i (x : X) = x := by
  constructor
  · intro hx i
    exact (CatalogueBFixedCentralQuotient.displacement_eq_one_iff Z (ψ i) (hinv i) hZ
      ⟨x, fixedPreimage_le Z ψ hinv i x.property⟩).mp (congrFun hx i)
  · intro hx
    funext i
    exact (CatalogueBFixedCentralQuotient.displacement_eq_one_iff Z (ψ i) (hinv i) hZ
      ⟨x, fixedPreimage_le Z ψ hinv i x.property⟩).mpr (hx i)

theorem displacement_kernel (hZ : Z ≤ Subgroup.center X) :
    (displacement Z ψ hinv hZ).ker = (commonFixed ψ).subgroupOf (fixedPreimage Z ψ hinv) := by
  ext x
  rw [MonoidHom.mem_ker, displacement_eq_one_iff]
  change (∀ i, ψ i (x : X) = x) ↔ (x : X) ∈ commonFixed ψ
  exact ⟨fun h => Subgroup.mem_iInf.mpr h, fun h => Subgroup.mem_iInf.mp h⟩

@[expose] def projection : fixedPreimage Z ψ hinv →* quotientFixed Z ψ hinv where
  toFun x := ⟨(QuotientGroup.mk' Z) x, x.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _

theorem projection_surjective : Function.Surjective (projection Z ψ hinv) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z (y : X ⧸ Z)
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change (QuotientGroup.mk' Z) x ∈ quotientFixed Z ψ hinv
  rw [hx]
  exact y.property

theorem commutator_fixedPreimage_le_commonFixed (hZ : Z ≤ Subgroup.center X) :
    ⁅fixedPreimage Z ψ hinv, fixedPreimage Z ψ hinv⁆ ≤ commonFixed ψ := by
  rw [commonFixed]
  exact le_iInf fun i =>
    (Subgroup.commutator_mono (fixedPreimage_le Z ψ hinv i)
      (fixedPreimage_le Z ψ hinv i)).trans
      (CatalogueBFixedCentralQuotient.commutator_fixedPreimage_le_fixedSubgroup
        Z (ψ i) (hinv i) hZ)

theorem map_commutator_fixedPreimage_eq :
    (⁅fixedPreimage Z ψ hinv, fixedPreimage Z ψ hinv⁆).map (QuotientGroup.mk' Z) =
      ⁅quotientFixed Z ψ hinv, quotientFixed Z ψ hinv⁆ := by
  rw [Subgroup.map_commutator]
  simp only [fixedPreimage,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)
      (quotientFixed Z ψ hinv)]

end CFSG.GroupTheory.FixedCentralQuotientFamily

end
