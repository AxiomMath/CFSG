module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrCenter

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open scoped commutatorElement

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

private lemma eq_of_mem_center_card_two {Q : Type*} [Group Q]
    (hcard : Nat.card (Subgroup.center Q) = 2) {u v : Q}
    (hu : u ∈ Subgroup.center Q) (hv : v ∈ Subgroup.center Q) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v := by
  obtain ⟨m, hm, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q)).mp hcard
  exact Subtype.ext_iff.mp ((huniq ⟨u, hu⟩ (by simpa using hu1)).trans
    (huniq ⟨v, hv⟩ (by simpa using hv1)).symm)

private lemma eq_of_mem_centerOf_card_two {C : Type*} [Group C] {Q : Subgroup C}
    (hcard : Nat.card (Subgroup.center ↥Q) = 2) {u v : C}
    (hu : u ∈ centerOf Q) (hv : v ∈ centerOf Q) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v := by
  obtain ⟨huQ, huc⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨hvQ, hvc⟩ := Subgroup.mem_inf.mp hv
  have hu_center : (⟨u, huQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_iff.mp huc (x : C) x.2
  have hv_center : (⟨v, hvQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_iff.mp hvc (x : C) x.2
  have hu_ne : (⟨u, huQ⟩ : ↥Q) ≠ 1 := by
    intro h
    exact hu1 (by simpa using congrArg Subtype.val h)
  have hv_ne : (⟨v, hvQ⟩ : ↥Q) ≠ 1 := by
    intro h
    exact hv1 (by simpa using congrArg Subtype.val h)
  have hEq := eq_of_mem_center_card_two hcard hu_center hv_center hu_ne hv_ne
  simpa using congrArg Subtype.val hEq

theorem exists_mul_mem_centralizer {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]
    (hQ : IsPlusExtraspecial 4 Q) {q : C} (hqQ : q ∈ Q) (hq : q ∉ centerOf Q) {g : C}
    (hg : ⁅g, q⁆ ∈ centerOf Q) :
    ∃ y ∈ Q, y * g ∈ Subgroup.centralizer ({q} : Set C) := by
  haveI hExt : CFSG.IsExtraspecial 2 ↥Q := hQ.1
  have hcard : Nat.card (Subgroup.center ↥Q) = 2 := hExt.center_order_p
  by_cases hζ1 : ⁅g, q⁆ = 1
  · refine ⟨1, Q.one_mem, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, one_mul]
    exact commutatorElement_eq_one_iff_mul_comm.mp hζ1
  · have hq_not_cent : q ∉ Subgroup.centralizer (Q : Set C) := fun h =>
      hq (Subgroup.mem_inf.mpr ⟨hqQ, h⟩)
    rw [Subgroup.mem_centralizer_iff] at hq_not_cent
    push_neg at hq_not_cent
    obtain ⟨y₀, hy₀Q, hy₀ne⟩ := hq_not_cent
    have hζ₀1 : ⁅y₀, q⁆ ≠ 1 := fun h =>
      hy₀ne (commutatorElement_eq_one_iff_mul_comm.mp h)
    have hζ₀mem : ⁅y₀, q⁆ ∈ centerOf Q := commutatorElement_mem_centerOf hQ hy₀Q hqQ
    have heq : ⁅y₀, q⁆ = ⁅g, q⁆ :=
      eq_of_mem_centerOf_card_two hcard hζ₀mem hg hζ₀1 hζ1
    refine ⟨y₀⁻¹, Q.inv_mem hy₀Q, ?_⟩
    have hgconj : g * q * g⁻¹ = ⁅g, q⁆ * q := by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
    have hy0conj : y₀ * q * y₀⁻¹ = ⁅g, q⁆ * q := by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul, heq]
    have hconj : y₀⁻¹ * (⁅g, q⁆ * q) * y₀ = q := by
      calc y₀⁻¹ * (⁅g, q⁆ * q) * y₀ = y₀⁻¹ * (y₀ * q * y₀⁻¹) * y₀ := by rw [hy0conj]
        _ = q := by group
    have hfinal : (y₀⁻¹ * g) * q * (y₀⁻¹ * g)⁻¹ = q := by
      calc (y₀⁻¹ * g) * q * (y₀⁻¹ * g)⁻¹ = y₀⁻¹ * (g * q * g⁻¹) * y₀ := by group
        _ = y₀⁻¹ * (⁅g, q⁆ * q) * y₀ := by rw [hgconj]
        _ = q := hconj
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (fun t => t * (y₀⁻¹ * g)) hfinal
    simpa [mul_assoc] using this

end CFSG.EvenSporadicStandard.HNRecog.Section3
