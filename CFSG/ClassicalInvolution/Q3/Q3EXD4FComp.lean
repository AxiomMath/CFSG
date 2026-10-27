module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4Local
public import CFSG.ClassicalInvolution.Q3.Q3NGInv
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourCaseI
public import CFSG.ClassicalInvolution.Q3.Q3WAStarMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)
open scoped MatrixGroups


section Commutator

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_commutator_eq_involution3 (hex : ExactMembers3 Ω) {N : Subgroup G}
    (hN : N ∈ Ω) {z : G} (hz : IsClassicalMember3 N z) :
    ∃ a ∈ N, ∃ b ∈ N, a * b * a⁻¹ * b⁻¹ = z := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex N hN)
  obtain ⟨a₀, b₀, hab⟩ : ∃ a₀ b₀ : SL(2, ZMod 3), a₀ * b₀ * a₀⁻¹ * b₀⁻¹ = -1 := by
    decide +kernel
  have hinv : ∀ s : SL(2, ZMod 3), s * s = 1 → s ≠ 1 → s = -1 := by decide +kernel
  have hz2 : z * z = 1 := by
    have h3 : z ^ 2 = 1 := by
      rw [← hz.orderOf_eq_two]
      exact pow_orderOf_eq_one _
    simpa [pow_two] using h3
  have hsq : e ⟨z, hz.mem⟩ * e ⟨z, hz.mem⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hz.mem⟩ : N) * ⟨z, hz.mem⟩ = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hne : e ⟨z, hz.mem⟩ ≠ 1 := by
    intro h
    have h1 : (⟨z, hz.mem⟩ : N) = 1 := e.injective (h.trans e.map_one.symm)
    have h2 : z = 1 := congrArg Subtype.val h1
    have := hz.orderOf_eq_two
    rw [h2, orderOf_one] at this
    omega
  have hez : e ⟨z, hz.mem⟩ = -1 := hinv _ hsq hne
  refine ⟨(e.symm a₀ : G), (e.symm a₀).2, (e.symm b₀ : G), (e.symm b₀).2, ?_⟩
  have h1 : e.symm (a₀ * b₀ * a₀⁻¹ * b₀⁻¹) = ⟨z, hz.mem⟩ := by
    rw [hab, ← hez, MulEquiv.symm_apply_apply]
  have h2 : e.symm (a₀ * b₀ * a₀⁻¹ * b₀⁻¹) = e.symm a₀ * e.symm b₀ * (e.symm a₀)⁻¹ *
      (e.symm b₀)⁻¹ := by
    simp only [map_mul, map_inv]
  rw [h2] at h1
  exact congrArg Subtype.val h1

end Commutator

section Comp

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem locMk_ne_one_of_involution3 {T : Subgroup G} {a : G} (ha : IsClassicalMember3 T a)
    (haY : a ∈ locLayer Ω x) : locMk Ω x ⟨a, haY⟩ ≠ 1 := by
  intro h
  have hO : (⟨a, haY⟩ : ↥(locLayer Ω x)) ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
    (QuotientGroup.eq_one_iff _).mp h
  have h2 : orderOf (⟨a, haY⟩ : ↥(locLayer Ω x)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ha.orderOf_eq_two
  have h3 := orderOf_dvd_natCard
    (⟨⟨a, haY⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
  have h4 : orderOf (⟨⟨a, haY⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  rw [h4] at h3
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card
    (↥(locLayer Ω x)))) (even_iff_two_dvd.mpr h3)

theorem locImg_not_commutes_u (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) : ¬ Commutes (locImg Ω x N) (locImg Ω x N) := by
  intro h
  obtain ⟨z, hz⟩ := hΩ.classical N hN.1
  obtain ⟨a, ha, b, hb, hab⟩ := exists_commutator_eq_involution3 hex hN.1 hz
  have haY : a ∈ locLayer Ω x := le_centralizingLayer hN ha
  have hbY : b ∈ locLayer Ω x := le_centralizingLayer hN hb
  have hzY : z ∈ locLayer Ω x := le_centralizingLayer hN hz.mem
  apply locMk_ne_one_of_involution3 hz hzY
  have hc := h _ ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩ _
    ⟨⟨b, hbY⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hzeq : (⟨z, hzY⟩ : ↥(locLayer Ω x)) =
      ⟨a, haY⟩ * ⟨b, hbY⟩ * ⟨a, haY⟩⁻¹ * ⟨b, hbY⟩⁻¹ := Subtype.ext hab.symm
  rw [hzeq]
  simp only [map_mul, map_inv]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  exact hc

theorem eq_of_locImg_le_range_u (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i j : ι} {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) (hi : locImg Ω x N ≤ (D.hom i).range)
    (hj : locImg Ω x N ≤ (D.hom j).range) : i = j := by
  by_contra hij
  exact locImg_not_commutes_u hΩ hex hN fun a ha b hb =>
    commutes_range3 D hij a (hi ha) b (hj hb)

theorem exists_unique_comp_u (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) : ∃! i, N ∈ compMembers3 Ω x D i := by
  obtain ⟨i, hi⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  exact ⟨i, ⟨hN, hi⟩, fun j hj => eq_of_locImg_le_range_u hΩ hex D hN hj.2 hi⟩

theorem exists_corr_left_u (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι} {N : Subgroup G}
    (hN : N ∈ compMembers3 Ω x D i) : ∃ R, Corr3 Ω x D i N R := by
  obtain ⟨hNm, hi⟩ := hN
  obtain ⟨j, R, hR, hRN⟩ := D.fundamental _ (mem_locFamily_iff.mpr ⟨N, hNm, rfl⟩)
  have hj : locImg Ω x N ≤ (D.hom j).range := hRN ▸ Subgroup.map_le_range _ _
  have hij := eq_of_locImg_le_range_u hΩ hex D hNm hj hi
  subst hij
  exact ⟨R, hNm, hR, hRN⟩

end Comp

section Odd

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)}

theorem comm_mem_oddCoreIn_of_ne_comp3 (hΩ : ConjInvariant Ω) {u : G}
    {D : LieSystemData3 ι (locQuot Ω u) (locFamily Ω u)} {i j : ι} (hij : i ≠ j)
    {N N' : Subgroup G} (hN : N ∈ compMembers3 Ω u D i) (hN' : N' ∈ compMembers3 Ω u D j)
    {a b : G} (ha : a ∈ N) (hb : b ∈ N') :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G)) := by
  have haY : a ∈ locLayer Ω u := le_centralizingLayer hN.1 ha
  have hbY : b ∈ locLayer Ω u := le_centralizingLayer hN'.1 hb
  have hc := commutes_range3 D hij (locMk Ω u ⟨a, haY⟩)
    (hN.2 ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩) (locMk Ω u ⟨b, hbY⟩)
    (hN'.2 ⟨⟨b, hbY⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩)
  have hd : (⟨a, haY⟩ * ⟨b, hbY⟩ * ⟨a, haY⟩⁻¹ * ⟨b, hbY⟩⁻¹ : ↥(locLayer Ω u)) ∈
      classicalInvolutionOddCore ↥(locLayer Ω u) := by
    rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥(locLayer Ω u))]
    change locMk Ω u (⟨a, haY⟩ * ⟨b, hbY⟩ * ⟨a, haY⟩⁻¹ * ⟨b, hbY⟩⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hc
  have := map_inclusion_oddCore_le (a := u) hΩ ⟨_, hd, rfl⟩
  exact ⟨_, this, rfl⟩

theorem le_commModOdd_of_ne_comp3 (hΩ : ConjInvariant Ω) {u : G}
    {D : LieSystemData3 ι (locQuot Ω u) (locFamily Ω u)} {i : ι} {X : Subgroup G}
    (hX : X ∈ compMembers3 Ω u D i) {𝒮 : Set (Subgroup G)}
    (h𝒮 : ∀ L ∈ 𝒮, L ∈ centralizingMembers Ω {u} ∧ ∀ j, L ∈ compMembers3 Ω u D j → j ≠ i)
    (hle : ∀ L ∈ 𝒮, ∃ j, L ∈ compMembers3 Ω u D j) :
    (⨆ L ∈ 𝒮, L) ≤ commModOdd u X := by
  refine iSup₂_le fun L hL g hg => ?_
  obtain ⟨j, hj⟩ := hle L hL
  refine ⟨(h𝒮 L hL).1.2 hg, fun y hy => ?_⟩
  exact comm_mem_oddCoreIn_of_ne_comp3 hΩ ((h𝒮 L hL).2 j hj) hj hX hg hy

theorem conjSub_mem_compMembers_of_oddCoreIn3 (hΩ : ConjInvariant Ω) {u : G}
    {D : LieSystemData3 ι (locQuot Ω u) (locFamily Ω u)} {i : ι} {N : Subgroup G}
    (hN : N ∈ compMembers3 Ω u D i) {n : G}
    (hn : n ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G))) :
    conjSub n N ∈ compMembers3 Ω u D i := by
  have hnC : n ∈ Subgroup.centralizer ({u} : Set G) := oddCoreIn_le _ hn
  refine ⟨⟨hΩ n N hN.1.1, ?_⟩, ?_⟩
  · intro y hy
    rw [mem_conjSub_iff] at hy
    have h1 := hN.1.2 hy
    have e : y = n * (n⁻¹ * y * n) * n⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnC h1) (Subgroup.inv_mem _ hnC)
  · refine le_trans ?_ hN.2
    rintro _ ⟨a, ha, rfl⟩
    have haN : (a : G) ∈ conjSub n N := Subgroup.mem_subgroupOf.mp ha
    rw [mem_conjSub_iff] at haN
    have hy₀Y : n⁻¹ * (a : G) * n ∈ locLayer Ω u := le_centralizingLayer hN.1 haN
    refine ⟨⟨n⁻¹ * (a : G) * n, hy₀Y⟩, Subgroup.mem_subgroupOf.mpr haN, ?_⟩
    show locMk Ω u ⟨n⁻¹ * (a : G) * n, hy₀Y⟩ = locMk Ω u a
    refine QuotientGroup.eq.mpr ?_
    have haC : (a : G) ∈ Subgroup.centralizer ({u} : Set G) :=
      centralizingLayer_le_centralizer Ω {u} a.2
    have hmem : (n⁻¹ * (a : G) * n)⁻¹ * (a : G) ∈
        oddCoreIn (Subgroup.centralizer ({u} : Set G)) := by
      have e : (n⁻¹ * (a : G) * n)⁻¹ * (a : G) = n⁻¹ * ((a : G)⁻¹ * n * (a : G)⁻¹⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hn)
        (conj_mem_oddCoreIn (Subgroup.inv_mem _ haC) hn)
    exact oddCoreIn_inf_layer_le u hmem
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy₀Y) a.2)

theorem locMk_eq_of_involutions3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G}
    {N N' : Subgroup G} (hN : N ∈ centralizingMembers Ω {x})
    (hN' : N' ∈ centralizingMembers Ω {x}) (himg : locImg Ω x N = locImg Ω x N') {w w' : G}
    (hw : IsClassicalMember3 N w) (hw' : IsClassicalMember3 N' w')
    (hwY : w ∈ locLayer Ω x) (hw'Y : w' ∈ locLayer Ω x) :
    locMk Ω x ⟨w, hwY⟩ = locMk Ω x ⟨w', hw'Y⟩ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_locImg3 hΩ hex hN
  obtain ⟨hwY₀, hwA, hw2, hw1, hwc⟩ := image_involution_facts3 hN hw
  obtain ⟨hw'Y₀, hwA', hw2', hw1', hwc'⟩ := image_involution_facts3 hN' hw'
  have key : ∀ (a : locQuot Ω x) (ha : a ∈ locImg Ω x N),
      (∀ y ∈ locImg Ω x N, a * y = y * a) → a ≠ 1 → e ⟨a, ha⟩ = -1 := by
    intro a ha hc h1
    have hcen : (⟨a, ha⟩ : locImg Ω x N) ∈ Subgroup.center (locImg Ω x N) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hc y y.2).symm
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp
      ((CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e _).mp hcen) with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm) :
        (⟨a, ha⟩ : locImg Ω x N) = 1)) h1
    · exact h
  have hwA'' : locMk Ω x ⟨w', hw'Y⟩ ∈ locImg Ω x N := himg ▸ hwA'
  have h1 := key _ hwA hwc hw1
  have h2 := key _ hwA'' (fun y hy => hwc' y (himg ▸ hy)) hw1'
  exact congrArg Subtype.val (e.injective (h1.trans h2.symm))

end Odd

end CFSG.ClassicalInvolution.Q3.Q3W.EX
