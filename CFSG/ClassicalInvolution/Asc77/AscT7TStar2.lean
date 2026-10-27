module

public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace T7T

variable {G : Type} [Group G] [Finite G]

theorem oddCoreOf_inf_le {H H' : Subgroup G} (hHH' : H ≤ H') {c : ↥H}
    (hc : (c : G) ∈ oddCoreOf H') : c ∈ classicalInvolutionOddCore ↥H := by
  let N₀ : Subgroup ↥H := (oddCoreOf H').subgroupOf H
  have hnorm : N₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    unfold oddCoreOf at hn ⊢
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨(⟨g, hHH' g.2⟩ : ↥H') * m * (⟨g, hHH' g.2⟩ : ↥H')⁻¹,
      (inferInstance : (classicalInvolutionOddCore ↥H').Normal).conj_mem m hm _, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.subtype_apply] at hmn ⊢
    rw [hmn]
  have hodd : Odd (Nat.card N₀) := by
    have hO : Odd (Nat.card (classicalInvolutionOddCore ↥H')) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥H'
    let ι : ↥N₀ →* ↥H' := (Subgroup.inclusion hHH').comp N₀.subtype
    have hι : ∀ n : ↥N₀, ι n ∈ classicalInvolutionOddCore ↥H' := by
      intro n
      have hn := n.2
      rw [Subgroup.mem_subgroupOf] at hn
      unfold oddCoreOf at hn
      obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hn
      have : ι n = m := Subtype.ext (by simpa [ι] using hmn.symm)
      rw [this]; exact hm
    let ι' : ↥N₀ →* ↥(classicalInvolutionOddCore ↥H') := ι.codRestrict _ hι
    have hinj : Function.Injective ι' := by
      intro x y hxy
      have h1 : ι x = ι y := congrArg Subtype.val hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa [ι] using congrArg Subtype.val h1
    have hdvd : Nat.card N₀ ∣ Nat.card (classicalInvolutionOddCore ↥H') :=
      Subgroup.card_dvd_of_injective ι' hinj
    exact Odd.of_dvd_nat hO hdvd
  exact le_sSup
    (show N₀ ∈ {N : Subgroup ↥H | N.Normal ∧ Odd (Nat.card N)} from ⟨hnorm, hodd⟩)
    (Subgroup.mem_subgroupOf.mpr hc)

theorem mem_zStarOf_of_le {H H' : Subgroup G} (hHH' : H ≤ H') {z : G} (hz : z ∈ zStarOf H')
    (hzH : z ∈ H) : z ∈ zStarOf H := by
  unfold zStarOf at hz ⊢
  obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_comap] at hh'
  refine Subgroup.mem_map.mpr ⟨⟨H'.subtype h', hzH⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro c
  obtain ⟨c0, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥H) c0, ← map_mul, ← map_mul,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  apply oddCoreOf_inf_le hHH'
  have hc := Subgroup.mem_center_iff.mp hh'
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥H') ⟨c0, hHH' c0.2⟩)
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hc
  refine Subgroup.mem_map.mpr ⟨_, hc, ?_⟩
  simp

theorem mem_zStarOf_centralizer_self (z : G) :
    z ∈ zStarOf (Subgroup.centralizer ({z} : Set G)) := by
  unfold zStarOf
  have hz : z ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine Subgroup.mem_map.mpr ⟨⟨z, hz⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro c
  obtain ⟨c0, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set G)))
    c0, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have := Subgroup.mem_centralizer_singleton_iff.mp c0.2
  simpa using this

end T7T

end CFSG.ClassicalInvolution.Asc77
