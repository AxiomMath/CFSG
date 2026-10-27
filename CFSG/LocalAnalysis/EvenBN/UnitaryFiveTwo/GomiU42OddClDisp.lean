module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_fixed_onQuotient_dvd {X : Type*} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z) :
    Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) ∣
      Nat.card (fixedSubgroup ψ) := by
  set D := CatalogueBFixedCentralQuotient.fixedPreimage Z ψ hinv with hD
  set pp := CatalogueBFixedCentralQuotient.preimageProjection Z ψ hinv with hpp
  set disp := CatalogueBFixedCentralQuotient.displacement Z ψ hinv hcentral with hdisp
  have hZD : Z ≤ D := CatalogueBFixedCentralQuotient.central_le_fixedPreimage Z ψ hinv
  have hFD : fixedSubgroup ψ ≤ D := CatalogueBFixedCentralQuotient.fixed_le_fixedPreimage Z ψ hinv
  have hker : pp.ker = Z.subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hrange : pp.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (CatalogueBFixedCentralQuotient.preimageProjection_surjective Z ψ hinv)
  have h1 : Nat.card D = Nat.card (fixedSubgroup
      (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) * Nat.card Z := by
    have := Subgroup.card_ker_mul_card_range pp
    rw [hker, hrange, Subgroup.card_top,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv] at this
    rw [← this, mul_comm]
  have h2 : Nat.card D = Nat.card (fixedSubgroup ψ) * Nat.card disp.range := by
    have := Subgroup.card_ker_mul_card_range disp
    rw [hdisp, CatalogueBFixedCentralQuotient.displacement_kernel Z ψ hinv hcentral,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFD).toEquiv] at this
    exact this.symm
  obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card disp.range
  have hr : 0 < Nat.card disp.range := Nat.card_pos
  refine ⟨m, ?_⟩
  have h3 : Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) *
      Nat.card Z = Nat.card (fixedSubgroup ψ) * Nat.card disp.range := h1 ▸ h2
  rw [hm] at h3
  have h4 : Nat.card (fixedSubgroup ψ) * Nat.card disp.range =
      (Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) * m) *
        Nat.card disp.range := by
    rw [← h3]; ring
  exact Nat.eq_of_mul_eq_mul_right hr h4

theorem card_fixed_onQuotient_eq_of_displacement {X : Type*} [Group X] [Finite X]
    (Z : Subgroup X) [Z.Normal] (hcentral : Z ≤ Subgroup.center X) (ψ : MulAut X)
    (hinv : Z.map ψ.toMonoidHom = Z) (hZ2 : Nat.card Z = 2) {x z : X} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hx : ψ x = x * z) :
    Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) =
      Nat.card (fixedSubgroup ψ) := by
  set D := CatalogueBFixedCentralQuotient.fixedPreimage Z ψ hinv with hD
  set pp := CatalogueBFixedCentralQuotient.preimageProjection Z ψ hinv with hpp
  set disp := CatalogueBFixedCentralQuotient.displacement Z ψ hinv hcentral with hdisp
  have hZD : Z ≤ D := CatalogueBFixedCentralQuotient.central_le_fixedPreimage Z ψ hinv
  have hFD : fixedSubgroup ψ ≤ D := CatalogueBFixedCentralQuotient.fixed_le_fixedPreimage Z ψ hinv
  have hker : pp.ker = Z.subgroupOf D := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hrange : pp.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (CatalogueBFixedCentralQuotient.preimageProjection_surjective Z ψ hinv)
  have h1 : Nat.card D = Nat.card (fixedSubgroup
      (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) * Nat.card Z := by
    have := Subgroup.card_ker_mul_card_range pp
    rw [hker, hrange, Subgroup.card_top,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv] at this
    rw [← this, mul_comm]
  have h2 : Nat.card D = Nat.card (fixedSubgroup ψ) * Nat.card disp.range := by
    have := Subgroup.card_ker_mul_card_range disp
    rw [hdisp, CatalogueBFixedCentralQuotient.displacement_kernel Z ψ hinv hcentral,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFD).toEquiv] at this
    exact this.symm
  have hxD : x ∈ D := by
    rw [hD, CatalogueBFixedCentralQuotient.mem_fixedPreimage_iff]
    have : x⁻¹ * ψ x = z := by rw [hx]; group
    rw [this]; exact hz
  have hmem : (⟨z, hz⟩ : Z) ∈ disp.range := by
    refine ⟨⟨x, hxD⟩, ?_⟩
    apply Subtype.ext
    change x⁻¹ * ψ x = z
    rw [hx]; group
  have hr2 : Nat.card disp.range = 2 := by
    obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card disp.range
    rw [hZ2] at hm
    have hpos : 0 < Nat.card disp.range := Nat.card_pos
    have hne : Nat.card disp.range ≠ 1 := by
      intro h1'
      have := Subgroup.card_eq_one.mp h1'
      rw [this, Subgroup.mem_bot] at hmem
      exact hz1 (congrArg Subtype.val hmem)
    have hle : Nat.card disp.range ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨m, hm⟩
    omega
  have h3 : Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) *
      Nat.card Z = Nat.card (fixedSubgroup ψ) * Nat.card disp.range := h1 ▸ h2
  rw [hr2, hZ2] at h3
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
