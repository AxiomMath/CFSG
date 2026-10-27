module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrPerm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrStabT

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open scoped commutatorElement

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

theorem exists_stabilizer_alternating {C : Type} [Group C] [Finite C] {Q : Subgroup C} [Q.Normal]
    (hQ : IsExtraspecialPlusByA5WrTwoWith C Q) (e : C ⧸ Q ≃* A5WrTwo) {q : C} (hqQ : q ∈ Q)
    (hq : q ∉ centerOf Q) (hsh : IsShapeTwoTwoSixS5 ↥(Subgroup.centralizer ({q} : Set C))) :
    ∃ S : Subgroup (↥(baseSub Q e) ⧸ Q.subgroupOf (baseSub Q e)),
      (∀ x, x ∈ S ↔ ∃ g : ↥(baseSub Q e),
        (g : ↥(baseSub Q e) ⧸ Q.subgroupOf (baseSub Q e)) = x ∧
          ⁅g, (⟨q, le_baseSub e hqQ⟩ : ↥(baseSub Q e))⁆ ∈ centerOf (Q.subgroupOf (baseSub Q e))) ∧
      Nonempty (↥S ≃* alternatingGroup (Fin 5)) := by
  let π : C →* A5WrTwo := (e : C ⧸ Q →* A5WrTwo).comp (QuotientGroup.mk' Q)
  let X : Subgroup C := Subgroup.centralizer ({q} : Set C)
  let H : Subgroup A5WrTwo := X.map π
  let K : Subgroup A5WrTwo := H ⊓ commutator A5WrTwo
  let Q' : Subgroup ↥(baseSub Q e) := Q.subgroupOf (baseSub Q e)
  let q' : ↥(baseSub Q e) := ⟨q, le_baseSub e hqQ⟩
  have hπQ : ∀ y ∈ Q, π y = 1 := by
    intro y hy
    have h1 : (QuotientGroup.mk y : C ⧸ Q) = 1 := (QuotientGroup.eq_one_iff y).2 hy
    simp [π, h1]
  have hKL : ∀ g : ↥(baseSub Q e), ⁅g, q'⁆ ∈ centerOf Q' ↔ π (g : C) ∈ H := by
    intro g
    have hcoe : ((⁅g, q'⁆ : ↥(baseSub Q e)) : C) = ⁅(g : C), q⁆ := by
      change (baseSub Q e).subtype ⁅g, q'⁆ = ⁅(g : C), q⁆
      rw [map_commutatorElement]
      rfl
    rw [mem_centerOf_subgroupOf_baseSub_iff e, hcoe]
    constructor
    · intro hg
      obtain ⟨y, hy, hyc⟩ := exists_mul_mem_centralizer hQ.plus hqQ hq hg
      have hmem : π (y * (g : C)) ∈ H :=
        Subgroup.mem_map.mpr ⟨y * (g : C), hyc, rfl⟩
      have heq : π (y * (g : C)) = π (g : C) := by rw [map_mul, hπQ y hy, one_mul]
      rwa [heq] at hmem
    · intro hg
      obtain ⟨t, ht, hπt⟩ := Subgroup.mem_map.mp hg
      have hcommtq : t * q = q * t := by
        have h1 := ht
        rw [Subgroup.mem_centralizer_iff] at h1
        exact (h1 q (Set.mem_singleton q)).symm
      have hcommt : ⁅t, q⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).2 hcommtq
      have hyQ : t⁻¹ * (g : C) ∈ Q := by
        rw [← QuotientGroup.eq_one_iff]
        apply e.injective
        rw [map_one]
        have h1 : π (t⁻¹ * (g : C)) = 1 := by
          rw [map_mul, map_inv, hπt, inv_mul_cancel]
        simpa [π] using h1
      have hcommy : ⁅t⁻¹ * (g : C), q⁆ ∈ centerOf Q :=
        commutatorElement_mem_centerOf hQ.plus hyQ hqQ
      have hge : (g : C) = t * (t⁻¹ * (g : C)) := by group
      rw [hge]
      have hcalc : ⁅t * (t⁻¹ * (g : C)), q⁆ = t * ⁅t⁻¹ * (g : C), q⁆ * t⁻¹ := by
        rw [commutatorElement_mul_left_eq_conj_mul, hcommt, mul_one]
      rw [hcalc]
      exact conj_mem_centerOf hcommy t
  have hmemdesc : ∀ x : ↥(baseSub Q e) ⧸ Q',
      x ∈ K.comap (psiBase Q e) ↔ ∃ g : ↥(baseSub Q e),
        (g : ↥(baseSub Q e) ⧸ Q') = x ∧ ⁅g, q'⁆ ∈ centerOf Q' := by
    intro x
    constructor
    · intro hx
      have hxK : psiBase Q e x ∈ K := hx
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x
      refine ⟨g, hg, ?_⟩
      have hπg : π (g : C) ∈ H := by
        have h1 : psiBase Q e (QuotientGroup.mk g) = π (g : C) := by
          rw [psiBase_mk]
          rfl
        rw [← hg] at hxK
        rw [h1] at hxK
        exact (Subgroup.mem_inf.mp hxK).1
      exact (hKL g).mpr hπg
    · rintro ⟨g, hg, hgc⟩
      have hπgH : π (g : C) ∈ H := (hKL g).mp hgc
      have hmem : psiBase Q e x ∈ K := by
        have h1 : psiBase Q e (QuotientGroup.mk g) = π (g : C) := by
          rw [psiBase_mk]
          rfl
        rw [← hg, h1]
        refine Subgroup.mem_inf.mpr ⟨hπgH, ?_⟩
        rw [← range_psiBase e]
        exact MonoidHom.mem_range.mpr ⟨QuotientGroup.mk g, h1.symm⟩
      exact hmem
  refine ⟨K.comap (psiBase Q e), hmemdesc, ?_⟩
  have hHperm : Nonempty (↥H ≃* Equiv.Perm (Fin 5)) :=
    exists_mulEquiv_map_centralizer_perm5 hQ e hqQ hq hsh
  have hKperm : Nonempty (↥K ≃* alternatingGroup (Fin 5)) :=
    exists_mulEquiv_inf_commutator_of_perm5 H hHperm
  have hKle : K ≤ (psiBase Q e).range := by
    intro x hx
    rw [range_psiBase]
    exact (Subgroup.mem_inf.mp hx).2
  have hmap : (K.comap (psiBase Q e)).map (psiBase Q e) = K :=
    Subgroup.map_comap_eq_self (f := psiBase Q e) (H := K) hKle
  obtain ⟨eK⟩ := hKperm
  exact ⟨(Subgroup.equivMapOfInjective _ (psiBase Q e) (psiBase_injective e)).trans
    ((MulEquiv.subgroupCongr hmap).trans eK)⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
