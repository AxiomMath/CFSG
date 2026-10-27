module

public import CFSG.RankThree.PartOne.S9.Planes.SecondCenter
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

theorem exists_secondCenterTorsion_characteristic
    {P : Type} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hP : IsPGroup p P) (hPnc : ¬ IsCyclic P) :
    ∃ W : Subgroup P, W.Characteristic ∧ ¬ IsCyclic W ∧
      (∀ x ∈ W, x ^ p = 1) ∧ ⁅⁅W, W⁆, W⁆ = ⊥ := by
  classical
  obtain ⟨hchar, hmem, hcentral, hnc⟩ :=
    CFSG.RankThree.PartOne.pgOddSecondCenterPrimeTorsion P p (Fact.out : p.Prime) hp2 hP
  let W : Subgroup P :=
    Subgroup.closure {x : P | x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1}
  have hWchar : W.Characteristic := hchar
  have hWnc : ¬ IsCyclic W := hnc hPnc
  have hWexp : ∀ x ∈ W, x ^ p = 1 := fun x hx => ((hmem x).1 hx).2
  have hWclass : ⁅⁅W, W⁆, W⁆ = ⊥ := by
    refine CFSG.RankThree.PartOne.Torsion37.commutator_commutator_eq_bot_of_central
      (W := W) (Q := ⊤) le_top ?_
    intro w hw g _ u _
    exact Subgroup.mem_center_iff.mp (hcentral w hw g).1 u
  exact ⟨W, hWchar, hWnc, hWexp, hWclass⟩

theorem exists_characteristic_noncyclic_exponent_classTwo
    {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) (hPnc : ¬ IsCyclic P) :
    ∃ D : Subgroup G, D ≤ P ∧ (D.subgroupOf P).Characteristic ∧ ¬ IsCyclic D ∧
      (∀ x ∈ D, x ^ p = 1) ∧ ⁅⁅D, D⁆, D⁆ = ⊥ := by
  classical
  obtain ⟨W, hWchar, hWnc, hWexp, hWclass⟩ :=
    exists_secondCenterTorsion_characteristic (p := p) hp2 hP hPnc
  let D : Subgroup G := W.map P.subtype
  have hDP : D ≤ P := Subgroup.map_subtype_le W
  have hDsub : D.subgroupOf P = W := by
    ext x
    simp [D, Subgroup.mem_subgroupOf]
  have hDchar : (D.subgroupOf P).Characteristic := by
    rw [hDsub]
    exact hWchar
  have hDnc : ¬ IsCyclic D := by
    intro hDcyc
    apply hWnc
    let e := W.equivMapOfInjective P.subtype P.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hDexp : ∀ x ∈ D, x ^ p = 1 := by
    rintro x ⟨w, hw, rfl⟩
    simpa using congrArg P.subtype (hWexp w hw)
  have hDclass : ⁅⁅D, D⁆, D⁆ = ⊥ := by
    change ⁅⁅W.map P.subtype, W.map P.subtype⁆, W.map P.subtype⁆ = ⊥
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hWclass, Subgroup.map_bot]
  exact ⟨D, hDP, hDchar, hDnc, hDexp, hDclass⟩

theorem exists_noncyclic_exponent_classTwo_normalized
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) (hPnc : ¬ IsCyclic P) :
    ∃ D : Subgroup G, D ≤ P ∧ D ≠ ⊥ ∧ ¬ IsCyclic D ∧ (∀ x ∈ D, x ^ p = 1) ∧
      ⁅⁅D, D⁆, D⁆ = ⊥ ∧
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  obtain ⟨D, hDP, hDchar, hDnc, hDexp, hDclass⟩ :=
    exists_characteristic_noncyclic_exponent_classTwo hp2 hP hPnc
  have hDne : D ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot D).1 (Nontrivial.of_not_isCyclic hDnc)
  have hnorm : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (D : Set G) := by
    have hmap : (D.subgroupOf P).map P.subtype = D :=
      Subgroup.map_subgroupOf_eq_of_le hDP
    have hle :=
      CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        P (D.subgroupOf P) hDchar
    simpa [hmap] using hle
  exact ⟨D, hDP, hDne, hDnc, hDexp, hDclass, hnorm⟩

end CFSG.GroupTheory
