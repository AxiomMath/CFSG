module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddCl
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddBasic
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Even
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Tags

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.mem_fixedSubgroup_iff (h : GomiU42Data X J D E a) (x : ↥D) :
    haveI := h.normal
    x ∈ fixedSubgroup (MulAut.conjNormal a : MulAut ↥D) ↔ (x : X) ∈ centralizer ({a} : Set X) := by
  haveI := h.normal
  change MulAut.conjNormal a x = x ↔ _
  rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, MulAut.conjNormal_apply]
  constructor
  · intro hx
    calc (x : X) * a = (a * x * a⁻¹) * a := by rw [hx]
      _ = a * x := by group
  · intro hx
    calc a * (x : X) * a⁻¹ = ((x : X) * a) * a⁻¹ := by rw [hx]
      _ = x := by group

theorem GomiU42Data.card_fixed_of_mem (h : GomiU42Data X J D E a) (ha : a ∈ D) :
    haveI := h.normal
    Nat.card ↥(fixedSubgroup (MulAut.conjNormal a : MulAut ↥D)) = 51840 := by
  haveI := h.normal
  have hCle : centralizer ({a} : Set X) ≤ D := by
    rw [← h.sup_eq]
    exact sup_le (zpowers_le.2 ha) h.le_D
  have h1 : (fixedSubgroup (MulAut.conjNormal a : MulAut ↥D)).map D.subtype =
      centralizer ({a} : Set X) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h.mem_fixedSubgroup_iff y).1 hy
    · intro hx
      have hxD : x ∈ D := hCle hx
      exact ⟨⟨x, hxD⟩, (h.mem_fixedSubgroup_iff ⟨x, hxD⟩).2 hx, rfl⟩
  have h2 : Nat.card ((fixedSubgroup (MulAut.conjNormal a : MulAut ↥D)).map D.subtype) =
      Nat.card ↥(fixedSubgroup (MulAut.conjNormal a : MulAut ↥D)) :=
    Subgroup.card_map_of_injective D.subtype_injective
  rw [h1, h.card_centralizer] at h2
  exact h2.symm

theorem GomiU42Data.card_fixed_of_not_mem (h : GomiU42Data X J D E a) (ha : a ∉ D) :
    haveI := h.normal
    Nat.card ↥(fixedSubgroup (MulAut.conjNormal a : MulAut ↥D)) = 25920 := by
  haveI := h.normal
  have h1 : fixedSubgroup (MulAut.conjNormal a : MulAut ↥D) = J.subgroupOf D := h.eqLocus_eq ha
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.lt.le).toEquiv]
  exact h.card_J

theorem GomiU42Data.u42Hyp (h : GomiU42Data X J D E a) :
    haveI := h.normal
    U42Hyp (MulAut.conjNormal a : MulAut ↥D)
      ((J.subgroupOf D).subgroupOf (fixedSubgroup (MulAut.conjNormal a : MulAut ↥D))) := by
  haveI := h.normal
  obtain ⟨-, -, hnormal, hinner⟩ := h.fixedRoot_conjNormal
  haveI := h.isSimpleGroup_J
  refine ⟨hnormal, h.fixedEquiv.isSimpleGroup, ?_, fun hσ => ?_, fun hσ => ?_⟩
  · rw [Nat.card_congr h.fixedEquiv.toEquiv]
    exact h.card_J
  · exact h.card_fixed_of_mem (hinner.2 hσ)
  · exact h.card_fixed_of_not_mem fun h' => hσ (hinner.1 h')

theorem GomiU42Data.card_fixed_quotient (h : GomiU42Data X J D E a) :
    haveI := h.normal
    Nat.card (((J.subgroupOf D).subgroupOf (fixedSubgroup (MulAut.conjNormal a : MulAut ↥D))) ⧸
      center ((J.subgroupOf D).subgroupOf (fixedSubgroup (MulAut.conjNormal a : MulAut ↥D)))) =
      25920 := by
  haveI := h.normal
  haveI := h.isSimpleGroup_J
  haveI : IsSimpleGroup ((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut ↥D))) := h.fixedEquiv.isSimpleGroup
  have hnab : ∃ x y : ((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut ↥D))), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := h.nonabelian_J
    refine ⟨h.fixedEquiv.symm x, h.fixedEquiv.symm y, fun h' => hxy ?_⟩
    have h'' := congrArg h.fixedEquiv h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h''
  rw [Nat.card_congr (quotientCenterEquivOfSimple hnab).toEquiv,
    Nat.card_congr h.fixedEquiv.toEquiv]
  exact h.card_J

theorem GomiU42Data.p_eq_three (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (h : GomiU42Data X J D E a) {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hm : LieModel ↥D t n p f) : p = 3 := by
  haveI := h.normal
  rcases hGLS ↥D t n p f hp hp2 hadm hm (MulAut.conjNormal a) h.fixedRoot_conjNormal.1 _
      h.isComponent_fixed with ⟨t', n', f', hadm', hmod'⟩ | ⟨h3, -, -, -⟩
  · obtain ⟨-, -, hfac⟩ := hO _ t' n' p f' hadm' hmod'
    rw [h.card_fixed_quotient] at hfac
    have hexp := CFSG.ComponentClassification.CatFC.e16_sylowExp_pos hadm'
    have hf' : 1 ≤ f' := hadm'.2.1
    have hpos : 1 ≤ lieSylowExponent t' n' * f' := Nat.mul_pos hexp hf'
    have hne : (25920 : ℕ).factorization p ≠ 0 := by omega
    rw [factorization_25920] at hne
    by_cases h3 : p = 3
    · exact h3
    by_cases h5 : p = 5
    · exfalso
      subst h5
      have h1 : lieSylowExponent t' n' * f' = 1 := by
        rw [← hfac, factorization_25920]; norm_num
      obtain ⟨rfl, rfl, rfl⟩ := CFSG.ComponentClassification.CatFC.e16_sylowExp_mul_eq_one hadm' h1
      obtain ⟨-, hord, -⟩ := hO _ .PSL 2 5 1 hadm' hmod'
      rw [h.card_fixed_quotient] at hord
      have h2 : lieOrderNumerator .PSL 2 (5 ^ 1) = 120 := by decide
      have h3' : lieOrderDivisor .PSL 2 (5 ^ 1) = 2 := by decide
      rw [h2, h3'] at hord
      omega
    · exfalso
      exact hne (by simp [hp2, h3, h5])
  · exact h3

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
