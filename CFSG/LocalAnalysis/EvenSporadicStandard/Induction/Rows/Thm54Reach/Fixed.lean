module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Transport

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open Subgroup CFSG CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_fixedComponent_conjNormal' {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    (hF : FStarSimple N) {t : Y} (ht : orderOf t = 2) {A : Subgroup Y}
    (hA : IsCompIn A (centralizer ({t} : Set Y))) (hAN : A ≤ N) :
    ∃ (σ : MulAut ↥N) (D : Subgroup ↥(fixedSubgroup σ)), orderOf σ = 2 ∧ IsComponent D ∧
      (σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range ↔ t ∈ N) ∧ Nonempty (↥D ≃* ↥A) ∧
      D.map (fixedSubgroup σ).subtype = A.subgroupOf N := by
  have := hF.normal
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  set σ : MulAut ↥N := MulAut.conjNormal t with hσdef
  have hσ2 : σ * σ = 1 := by rw [hσdef, ← map_mul, ht2, map_one]
  have hσ1 : σ ≠ 1 := CFSG.ComponentClassification.CatFC.conjNormal_ne_one hF ht1
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  have hfix : ∀ x : ↥N, x ∈ fixedSubgroup σ ↔ t * (x : Y) = x * t := by
    intro x
    change σ x = x ↔ _
    rw [← Subtype.coe_inj, hσdef, MulAut.conjNormal_apply]
    constructor
    · intro h
      calc t * (x : Y) = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [h]
    · intro h
      rw [h]
      group
  have hA'le : A.subgroupOf N ≤ fixedSubgroup σ := by
    intro x hx
    rw [hfix]
    exact (mem_centralizer_singleton_iff.1 (hA.1 (Subgroup.mem_subgroupOf.1 hx))).symm
  let e : ↥((A.subgroupOf N).subgroupOf (fixedSubgroup σ)) ≃* ↥A :=
    (Subgroup.subgroupOfEquivOfLe hA'le).trans (Subgroup.subgroupOfEquivOfLe hAN)
  refine ⟨σ, (A.subgroupOf N).subgroupOf (fixedSubgroup σ), hσo, ?_, ?_, ⟨e⟩,
    Subgroup.map_subgroupOf_eq_of_le hA'le⟩
  · let f : ↥(fixedSubgroup σ) →* ↥(centralizer ({t} : Set Y)) :=
      (N.subtype.comp (fixedSubgroup σ).subtype).codRestrict _ (fun x =>
        mem_centralizer_singleton_iff.2 ((hfix x.1).1 x.2).symm)
    have hcomap : (A.subgroupOf N).subgroupOf (fixedSubgroup σ) =
        (A.subgroupOf (centralizer ({t} : Set Y))).comap f := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      rfl
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hA.isQuasisimple, ?_⟩
    rw [hcomap]
    exact Subgroup.IsSubnormal.comap f hA.2.2
  · constructor
    · rintro ⟨n, hn⟩
      have key : (n : Y)⁻¹ * t ∈ centralizer (N : Set Y) := by
        rw [mem_centralizer_iff]
        intro x hx
        have h := congrArg (fun φ : MulAut ↥N => ((φ ⟨x, hx⟩ : ↥N) : Y)) hn
        simp only [hσdef, MulAut.conjNormal_apply, MulAut.conj_apply] at h
        have h' : (n : Y) * x * (n : Y)⁻¹ = t * x * t⁻¹ := h
        calc x * ((n : Y)⁻¹ * t)
            = (n : Y)⁻¹ * ((n : Y) * x * (n : Y)⁻¹) * t := by group
          _ = (n : Y)⁻¹ * (t * x * t⁻¹) * t := by rw [h']
          _ = (n : Y)⁻¹ * t * x := by group
      have h1 : (n : Y)⁻¹ * t ∈ N := hF.centralizer_le key
      have h2 : t = (n : Y) * ((n : Y)⁻¹ * t) := by group
      rw [h2]
      exact N.mul_mem n.2 h1
    · intro htN
      exact ⟨⟨t, htN⟩, MulEquiv.ext fun x => Subtype.ext (by
        simp [hσdef, MulAut.conjNormal_apply])⟩

theorem isComponent_centralizer_of_normal {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    {a : ↥N} {A : Subgroup Y} (hA : IsCompIn A (centralizer ({(a : Y)} : Set Y)))
    (hAN : A ≤ N) :
    IsComponent ((A.subgroupOf N).subgroupOf (centralizer ({a} : Set ↥N))) := by
  have hA'le : A.subgroupOf N ≤ centralizer ({a} : Set ↥N) := by
    intro x hx
    refine mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    exact (mem_centralizer_singleton_iff.1 (hA.1 (Subgroup.mem_subgroupOf.1 hx)))
  let e : ↥((A.subgroupOf N).subgroupOf (centralizer ({a} : Set ↥N))) ≃* ↥A :=
    (Subgroup.subgroupOfEquivOfLe hA'le).trans (Subgroup.subgroupOfEquivOfLe hAN)
  let f : ↥(centralizer ({a} : Set ↥N)) →* ↥(centralizer ({(a : Y)} : Set Y)) :=
    (N.subtype.comp (centralizer ({a} : Set ↥N)).subtype).codRestrict _ (fun x =>
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)))
  have hcomap : (A.subgroupOf N).subgroupOf (centralizer ({a} : Set ↥N)) =
      (A.subgroupOf (centralizer ({(a : Y)} : Set Y))).comap f := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hA.isQuasisimple, ?_⟩
  rw [hcomap]
  exact Subgroup.IsSubnormal.comap f hA.2.2

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
