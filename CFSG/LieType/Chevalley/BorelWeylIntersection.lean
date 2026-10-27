module

public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.WeylExchange

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type} [CommRing R]

theorem torusGroup_le_borelGroup
    : torusGroup τ R ≤ borelGroup τ R :=
  le_sup_left

theorem torusGroup_le_monomialSubgroup
    : torusGroup τ R ≤ monomialSubgroup τ R :=
  le_sup_left

theorem mem_torusGroup_of_isUpperTriangular
    [Nontrivial R] {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ monomialSubgroup τ R)
    (hup : IsUpperTriangular τ R (g : Module.End R (RootModule τ R))) : g ∈ torusGroup τ R := by
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hg
  have hmaps : MapsRootLines (k * canonicalRep (coxeterSystem τ) R w) w := by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  by_cases hw : w = 1
  · subst hw
    rwa [canonicalRep_one, mul_one]
  exfalso
  obtain ⟨i, hroot, hneg⟩ := (weyl_exchange_condition τ).2.2.2 w hw
  obtain ⟨c, hc⟩ := hmaps _ (isRoot_single τ i)
  have hprec : Label.Precedes (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩ : Label τ)
      (Sum.inr ⟨w • (Pi.single i 1 : Fin τ.rank → ℤ), hroot⟩) := by
    left
    change height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) < height (Pi.single i 1 : Fin τ.rank → ℤ)
    rw [height_single]
    omega
  have h0 := hup _ _ hprec
  rw [← rootVec_eq_single_of_isRoot (isRoot_single τ i), hc, rootVec_eq_single_of_isRoot hroot,
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h0
  exact c.ne_zero h0

theorem isUpperTriangular_iff_mem_torusGroup
    [Nontrivial R] {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ monomialSubgroup τ R) :
    IsUpperTriangular τ R (g : Module.End R (RootModule τ R)) ↔ g ∈ torusGroup τ R :=
  ⟨mem_torusGroup_of_isUpperTriangular hg, fun h =>
    (triangular_borel_structure.{0, 0} τ R).2.2.2.2.2.2.2.2.2.1 g (torusGroup_le_borelGroup h)⟩

theorem borel_weyl_intersection
    (τ : Tag) (R : Type) [CommRing R] [Nontrivial R] :
    borelGroup τ R ⊓ monomialSubgroup τ R = torusGroup τ R ∧
    posUnipotent τ R ⊓ monomialSubgroup τ R = ⊥ ∧
    ∀ g ∈ monomialSubgroup τ R,
      (IsUpperTriangular τ R (g : Module.End R (RootModule τ R)) ↔ g ∈ torusGroup τ R) := by
  have hBN : borelGroup τ R ⊓ monomialSubgroup τ R = torusGroup τ R := by
    refine le_antisymm (fun g hg => ?_) (le_inf torusGroup_le_borelGroup
      torusGroup_le_monomialSubgroup)
    obtain ⟨hgB, hgN⟩ := Subgroup.mem_inf.1 hg
    exact mem_torusGroup_of_isUpperTriangular hgN
      ((triangular_borel_structure.{0, 0} τ R).2.2.2.2.2.2.2.2.2.1 g hgB)
  refine ⟨hBN, ?_, fun g hg => isUpperTriangular_iff_mem_torusGroup hg⟩
  have hUB : posUnipotent τ R ≤ borelGroup τ R := le_sup_right
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgU, hgN⟩ := Subgroup.mem_inf.1 hg
  have hH : g ∈ torusGroup τ R := by
    rw [← hBN]
    exact Subgroup.mem_inf.2 ⟨hUB hgU, hgN⟩
  have h := Subgroup.mem_inf.2 ⟨hH, hgU⟩
  rwa [(triangular_borel_structure.{0, 0} τ R).2.2.2.1] at h

end CFSG.LieType.Chevalley
