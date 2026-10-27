module

public import CFSG.ClassicalInvolution.Q3.Q3URTransfer
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem locImg_self_le_Q₀U3 {m : ℕ} (hm : 2 ≤ m) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember3 K z) (d : ShapeUDict 3 1 m Ω z) : locImg Ω z K ≤ d.Q₀ := by
  have hk : 2 ≤ m + 1 := by omega
  have hn3 : 3 ≤ m + 1 := by omega
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  rcases d.fam_cases hk _ hmem with h | ⟨L, hL, hLK⟩
  · exact h
  · exfalso
    let zY : ↥(locLayer Ω z) := ⟨z, le_centralizingLayer hKz hz.mem⟩
    have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY ∈
        locImg Ω z K := ⟨zY, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
    rw [hLK] at hzK
    obtain ⟨r, hrR, hr⟩ := hzK
    have hcentral : ∀ w : locQuot Ω z,
        w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY * w := by
      intro w
      obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (centralizingLayer_le_centralizer Ω {z} w'.2)
    have hrc : r ∈ Subgroup.center (Su (GaloisField 3 2) 3 1 (m + 1)) := by
      have := isPerfect_su_three_le hn3
      refine mem_center_of_comm_mem_center fun s => d.ker_le ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hr]
      rw [commutatorElement_def, ← hcentral (d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨i, hi⟩ := hL
    have hr1 : r = 1 := by
      have hker : (QuotientGroup.mk' (Subgroup.center
          (Su (GaloisField 3 2) 3 1 (m + 1)))).ker ≤
          Subgroup.center (Su (GaloisField 3 2) 3 1 (m + 1)) := by
        rw [QuotientGroup.ker_mk']
      exact eq_one_of_mem_ker_of_isLongRootSU2_3 hn3 hi hker r hrR
        (by rw [QuotientGroup.ker_mk']; exact hrc)
    rw [hr1, map_one] at hr
    have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
      (QuotientGroup.eq_one_iff _).mp hr.symm
    have h2 : orderOf zY = 2 := by
      rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
    have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
    have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h2
    rw [h4] at h3
    have := (CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z)))
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)

theorem eq_of_locImg_le_Q₀U3 {m : ℕ} (hm : 2 ≤ m) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember3 K z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (d : ShapeUDict 3 1 m Ω z)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLQ : locImg Ω z L ≤ d.Q₀) :
    L = K := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hKQ := locImg_self_le_Q₀U3 hm hK hz d
  have hcL := card_locImg3 hΩ hex hL
  have hcK := card_locImg3 hΩ hex hKz
  have hcard := d.card_le
  rw [card_sl2_gf3] at hcard
  have e1 : locImg Ω z L = d.Q₀ := Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact hcard)
  have e2 : locImg Ω z K = d.Q₀ := Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcK]; exact hcard)
  exact locImg_injOn3 hΩ hex hP1 hO3 hL hKz (e1.trans e2.symm)

theorem exists_root_of_neU3 {m : ℕ} (hm : 2 ≤ m) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember3 K z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (d : ShapeUDict 3 1 m Ω z)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    ∃ R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) (by omega : 2 ≤ m + 1),
      locImg Ω z L = R.map d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases d.fam_cases (by omega) _ hmem with h | h
  · exact absurd (eq_of_locImg_le_Q₀U3 hm hΩ hex hK hz hP1 hO3 d hL h) hLK
  · exact h

theorem exists_member_of_rootU3 {m : ℕ} (hm : 2 ≤ m) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember3 K z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (d : ShapeUDict 3 1 m Ω z)
    {R : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))}
    (hR : R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) (by omega : 2 ≤ m + 1)) :
    ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = R.map d.ψ := by
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (d.mem_fam (by omega) R hR)
  refine ⟨L, hL, fun hLK => ?_, hLR⟩
  subst hLK
  have h1 : Commutes (locImg Ω z L) (locImg Ω z L) := by
    intro a ha b hb
    have hb' : b ∈ d.ψ.range := by
      rw [hLR] at hb
      obtain ⟨c, _, rfl⟩ := hb
      exact ⟨c, rfl⟩
    exact d.commutes a (locImg_self_le_Q₀U3 hm hK hz d ha) b hb'
  exact not_commutes_self3 hz (commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hL hL h1)

theorem commutes_K_of_neU3 {m : ℕ} (hm : 2 ≤ m) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember3 K z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (d : ShapeUDict 3 1 m Ω z)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) : Commutes K L := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  obtain ⟨R, hR, hLR⟩ := exists_root_of_neU3 hm hΩ hex hK hz hP1 hO3 d hL hLK
  refine commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hKz hL ?_
  have := d.commutes
  intro a ha b hb
  rw [hLR] at hb
  exact this a (locImg_self_le_Q₀U3 hm hK hz d ha) b
    (by obtain ⟨c, _, rfl⟩ := hb; exact ⟨c, rfl⟩)

theorem psiU_root_inv3 {m : ℕ} (hm : 2 ≤ m) {z : G} (d : ShapeUDict 3 1 m Ω z) {L : Subgroup G}
    {R : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))} {i : Su (GaloisField 3 2) 3 1 (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField 3 2) 3 1 (by omega : 2 ≤ m + 1) R i)
    (hLR : locImg Ω z L = R.map d.ψ) (hLY : L ≤ locLayer Ω z) {zL : G} (hzL : zL ∈ L)
    (h2 : orderOf zL = 2) : d.ψ i = locElt Ω z zL (hLY hzL) := by
  have himg : Transfer.IsLongRootSU2Image d.ψ (by omega : 2 ≤ m + 1) (locImg Ω z L) (d.ψ i) :=
    ⟨R, i, hRi, hLR.symm, rfl⟩
  exact (eq_of_orderOf_eq_two_of_image3 (by omega) d.ker_le himg (locElt_mem_locImg hLY hzL)
    (orderOf_locElt (hLY hzL) h2)).symm

end Members

structure UCtx3 (m : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G)
    extends UCore3 m Ω K z where
  hlift : m + 1 ≠ 4 ∨ Transfer.KerInvolutionFree d.ψ

namespace UCtx3

variable {m : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  (c : UCtx3 m Ω K z)

include c

theorem hn : 2 ≤ m + 1 := by have := c.hm; omega

theorem hn3 : 3 ≤ m + 1 := by have := c.hm; omega

theorem ker_cop : ∀ n ∈ c.d.ψ.ker, ¬ 3 ∣ orderOf n :=
  ker_orderOf_not_dvd_three_su3 c.hn3 c.d.ker_le

theorem pow_three_root {R : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))}
    {i : Su (GaloisField 3 2) 3 1 (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R i) : ∀ l ∈ R, l ^ 3 ∈ ⁅R, R⁆ := by
  obtain ⟨e⟩ := (hRi.isClassicalSL2 card_gf9 (by norm_num)).nonempty_mulEquiv
  exact pow_three_mem_commutator_of_equiv card_fixedSubfield_gf9 e

theorem commutes_of_commutes_map {R R' : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))}
    {i : Su (GaloisField 3 2) 3 1 (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R i)
    (h : Commutes (R.map c.d.ψ) (R'.map c.d.ψ)) : Commutes R R' := by
  intro a ha b hb
  exact (commutes_of_map_commute_exponent3 c.d.ψ (hker := c.d.ker_le) c.ker_cop
    (A := R') (L := R) (c.pow_three_root hRi)
    (fun a' ha' l hl => (h _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm

variable [Finite G]

theorem commutes_iff_root {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) {R R' : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))}
    {i : Su (GaloisField 3 2) 3 1 (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R i)
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact c.commutes_of_commutes_map hRi h1
  · intro h
    refine commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes _ h

theorem exists_rootData {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K)
    {zL : G} (hzL : IsClassicalMember3 L zL) :
    ∃ (R : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1)))
      (i : Su (GaloisField 3 2) 3 1 (m + 1)),
      IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R i ∧ locImg Ω z L = R.map c.d.ψ ∧
      c.d.ψ i = locElt Ω z zL (le_centralizingLayer hL hzL.mem) := by
  obtain ⟨R, hR, hLR⟩ := exists_root_of_neU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hL hLK
  obtain ⟨i, hi⟩ := hR
  exact ⟨R, i, hi, hLR, psiU_root_inv3 c.hm c.d hi hLR (le_centralizingLayer hL) hzL.mem
    hzL.orderOf_eq_two⟩

theorem stdpair_of_root {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) {R R' : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))}
    {i i' : Su (GaloisField 3 2) 3 1 (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R i)
    (hRi' : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R' i')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ)
    (hc : Commute i i') (hne : i ≠ i') (hnc : ¬ Commutes R R') :
    ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W L L' := by
  rcases lemma_6_5_su_map_of_commute3 c.hn3 c.d.ker_le hRi hRi' hc hne with h | ⟨-, h⟩
  · exact absurd (c.commutes_of_commutes_map hRi h) hnc
  · rw [← hLR, ← hLR'] at h
    exact unitaryBlockStandardPair_of_locImg3 c.hΩ c.hex c.hP1 c.hO3 hL hL' h

omit [Finite G] in
theorem rootInv_eq_of_locImg_eq {L L' : Subgroup G}
    {R R' : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))}
    {i i' : Su (GaloisField 3 2) 3 1 (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R i)
    (hRi' : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R' i')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ)
    (h : locImg Ω z L = locImg Ω z L') : i = i' := by
  have himg : Transfer.IsLongRootSU2Image c.d.ψ c.hn (locImg Ω z L') (c.d.ψ i') :=
    ⟨R', i', hRi', hLR'.symm, rfl⟩
  have hmem : c.d.ψ i ∈ locImg Ω z L' := by
    rw [← h, hLR]
    exact ⟨i, hRi.mem, rfl⟩
  have hord : orderOf (c.d.ψ i) = 2 := by
    have himg0 : Transfer.IsLongRootSU2Image c.d.ψ c.hn (locImg Ω z L) (c.d.ψ i) :=
      ⟨R, i, hRi, hLR.symm, rfl⟩
    exact orderOf_eq_two_of_image3 c.hn3 c.d.ker_le himg0
  have h1 := eq_of_orderOf_eq_two_of_image3 c.hn3 c.d.ker_le himg hmem hord
  exact eq_of_map_eq_of_isLongRootSU2_3 c.hn3 hRi hRi' c.d.ker_le c.hlift h1

theorem eq_of_rootInv_eq {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) {R R' : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))}
    {i : Su (GaloisField 3 2) 3 1 (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R i)
    (hRi' : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R' i)
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) : L = L' := by
  have hRR : R = R' := by
    rw [hRi.eq_longRootGroupSU two_ne_zero_gf9, hRi'.eq_longRootGroupSU two_ne_zero_gf9]
  exact locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL hL' (by rw [hLR, hLR', hRR])

theorem ne_of_rootInv {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (hne : L ≠ L')
    {R R' : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))}
    {i i' : Su (GaloisField 3 2) 3 1 (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R i)
    (hRi' : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn R' i')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) : i ≠ i' := by
  intro h
  subst h
  exact hne (c.eq_of_rootInv_eq hL hL' hRi hRi' hLR hLR')

end UCtx3

end CFSG.ClassicalInvolution.Q3.Q3W
