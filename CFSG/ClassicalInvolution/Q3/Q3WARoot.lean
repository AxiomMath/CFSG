module

public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.RouteD.LocalRoot

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

section Members

variable {G : Type} [Group G]

theorem not_commutes_self3 {K : Subgroup G} {z : G} (h : IsClassicalMember3 K z) :
    ¬ Commutes K K := by
  intro hc
  obtain ⟨e⟩ := h.nonempty_equiv
  have hcomm : ∀ a b : ↥K, a * b = b * a := fun a b => Subtype.ext (hc a a.2 b b.2)
  have hab : ∀ a b : SL(2, ZMod 3), a * b = b * a := by
    intro a b
    obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore K) (e.symm a)
    obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore K) (e.symm b)
    apply e.symm.injective
    rw [map_mul, map_mul, ← ha', ← hb', ← map_mul, ← map_mul, hcomm a' b']
  exact sl2Three_not_comm hab

theorem locImg_self_le_Q₀3 [Finite G] {m : ℕ} (hm : 2 ≤ m) {Ω : Set (Subgroup G)}
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember3 K z)
    (d : ShapeADict 3 1 m Ω z) : locImg Ω z K ≤ d.Q₀ := by
  have hk : 2 ≤ m + 1 := by omega
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  rcases d.fam_cases hk _ hmem with h | ⟨R, hR, hRK⟩
  · exact h
  · exfalso
    let zY : ↥(locLayer Ω z) := ⟨z, le_centralizingLayer hKz hz.mem⟩
    have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY ∈
        locImg Ω z K := ⟨zY, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
    rw [hRK] at hzK
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
    have hrc : r ∈ Subgroup.center SL(m + 1, GaloisField 3 1) := by
      have := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le
        (K := GaloisField 3 1) (n := m + 1) (by omega)
      refine mem_center_of_comm_mem_center fun s => d.ker_le ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hr]
      rw [commutatorElement_def, ← hcentral (d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨i, hi⟩ := hR
    have hr1 : r = 1 := by
      have hker : (QuotientGroup.mk' (Subgroup.center SL(m + 1, GaloisField 3 1))).ker ≤
          Subgroup.center SL(m + 1, GaloisField 3 1) := by
        rw [QuotientGroup.ker_mk']
      exact Transfer.eq_one_of_mem_ker_of_isLongRootSL2 odd_gf3 (by omega) hi hker r hrR
        (by rw [QuotientGroup.ker_mk']; exact hrc)
    rw [hr1, map_one] at hr
    have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
      (QuotientGroup.eq_one_iff _).mp hr.symm
    have h2 : orderOf zY = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hz.orderOf_eq_two
    have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
    have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact h2
    rw [h4] at h3
    have := CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z))
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)

theorem eq_of_locImg_le_Q₀3 [Finite G] {m : ℕ} (hm : 2 ≤ m) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember3 K z) (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    (d : ShapeADict 3 1 m Ω z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLQ : locImg Ω z L ≤ d.Q₀) : L = K := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hKQ := locImg_self_le_Q₀3 hm hK hz d
  have hcL := card_locImg3 hΩ hex hL
  have hcK := card_locImg3 hΩ hex hKz
  have hcard := d.card_le
  rw [card_sl2_gf3] at hcard
  have e1 : locImg Ω z L = d.Q₀ := Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact hcard)
  have e2 : locImg Ω z K = d.Q₀ := Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcK]; exact hcard)
  exact locImg_injOn3 hΩ hex hP1 hO3 hL hKz (e1.trans e2.symm)

theorem exists_root_of_ne3 [Finite G] {m : ℕ} (hm : 2 ≤ m) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember3 K z) (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    (d : ShapeADict 3 1 m Ω z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLK : L ≠ K) :
    ∃ R ∈ longRootSet (K := GaloisField 3 1) (by omega : 2 ≤ m + 1), locImg Ω z L = R.map d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases d.fam_cases (by omega) _ hmem with h | h
  · exact absurd (eq_of_locImg_le_Q₀3 hm hΩ hex hK hz hP1 hO3 d hL h) hLK
  · exact h

theorem exists_member_of_root3 [Finite G] {m : ℕ} (hm : 2 ≤ m) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember3 K z) (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    (d : ShapeADict 3 1 m Ω z) {R : Subgroup SL(m + 1, GaloisField 3 1)}
    (hR : R ∈ longRootSet (K := GaloisField 3 1) (by omega : 2 ≤ m + 1)) :
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
    exact d.commutes a (locImg_self_le_Q₀3 hm hK hz d ha) b hb'
  exact not_commutes_self3 hz (commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hL hL h1)

theorem commutes_K_of_ne3 [Finite G] {m : ℕ} (hm : 2 ≤ m) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember3 K z) (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    (d : ShapeADict 3 1 m Ω z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLK : L ≠ K) : Commutes K L := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  obtain ⟨R, hR, hLR⟩ := exists_root_of_ne3 hm hΩ hex hK hz hP1 hO3 d hL hLK
  refine commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hKz hL ?_
  have := d.commutes
  intro a ha b hb
  rw [hLR] at hb
  exact this a (locImg_self_le_Q₀3 hm hK hz d ha) b
    (by obtain ⟨c, _, rfl⟩ := hb; exact ⟨c, rfl⟩)

end Members

structure ACore3 (m : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) where
  hm : 2 ≤ m
  hΩ : InClass3 Ω
  hex : ExactMembers3 Ω
  hK : K ∈ Ω
  hz : IsClassicalMember3 K z
  hP1 : LocalOddCentral Ω {z}
  hO3 : LocalOddThreeFree3 Ω z
  d : ShapeADict 3 1 m Ω z

structure ACtx3 (m : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G)
    extends ACore3 m Ω K z where
  hlift : m + 1 ≠ 4 ∨ Transfer.KerInvolutionFree d.ψ

namespace ACtx3

variable {m : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  (c : ACtx3 m Ω K z)

include c

theorem hn : 2 ≤ m + 1 := by have := c.hm; omega

theorem hn3 : 3 ≤ m + 1 := by have := c.hm; omega

theorem ker_cop : ∀ n ∈ c.d.ψ.ker, ¬ 3 ∣ orderOf n :=
  ker_orderOf_not_dvd_three card_gf3 (by have := c.hm; omega) c.d.ker_le

theorem pow_three_root {R : Subgroup SL(m + 1, GaloisField 3 1)} {i : SL(m + 1, GaloisField 3 1)}
    (hRi : IsLongRootSL2 c.hn R i) : ∀ l ∈ R, l ^ 3 ∈ ⁅R, R⁆ := by
  obtain ⟨e⟩ := (hRi.isClassicalSL2 two_ne_zero_gf3).nonempty_mulEquiv
  exact pow_three_mem_commutator_of_equiv card_gf3 e

theorem commutes_of_commutes_map {R R' : Subgroup SL(m + 1, GaloisField 3 1)}
    {i : SL(m + 1, GaloisField 3 1)} (hRi : IsLongRootSL2 c.hn R i)
    (h : Commutes (R.map c.d.ψ) (R'.map c.d.ψ)) : Commutes R R' := by
  intro a ha b hb
  exact (commutes_of_map_commute_exponent3 c.d.ψ (hker := c.d.ker_le) c.ker_cop
    (A := R') (L := R) (c.pow_three_root hRi)
    (fun a' ha' l hl => (h _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm

theorem commutes_iff_root [Finite G] {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) {R R' : Subgroup SL(m + 1, GaloisField 3 1)}
    {i : SL(m + 1, GaloisField 3 1)} (hRi : IsLongRootSL2 c.hn R i)
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

theorem exists_rootData [Finite G] {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLK : L ≠ K) {zL : G} (hzL : IsClassicalMember3 L zL) :
    ∃ (R : Subgroup SL(m + 1, GaloisField 3 1)) (i : SL(m + 1, GaloisField 3 1)),
      IsLongRootSL2 c.hn R i ∧ locImg Ω z L = R.map c.d.ψ ∧
      c.d.ψ i = locElt Ω z zL (le_centralizingLayer hL hzL.mem) := by
  obtain ⟨R, hR, hLR⟩ := exists_root_of_ne3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hL hLK
  obtain ⟨i, hi⟩ := hR
  exact ⟨R, i, hi, hLR, psi_root_inv c.hm odd_gf3 c.d hi hLR (le_centralizingLayer hL) hzL.mem
    hzL.orderOf_eq_two⟩

theorem stdpair_of_root [Finite G] {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) {R R' : Subgroup SL(m + 1, GaloisField 3 1)}
    {i i' : SL(m + 1, GaloisField 3 1)} (hRi : IsLongRootSL2 c.hn R i)
    (hRi' : IsLongRootSL2 c.hn R' i') (hLR : locImg Ω z L = R.map c.d.ψ)
    (hLR' : locImg Ω z L' = R'.map c.d.ψ) (hc : Commute i i') (hne : i ≠ i')
    (hnc : ¬ Commutes R R') :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W L L' := by
  rcases lemma_6_5_map_of_commute3 card_gf3 c.hn3 c.d.ker_le hRi hRi' hc hne with h | ⟨-, h⟩
  · exact absurd (c.commutes_of_commutes_map hRi h) hnc
  · rw [← hLR, ← hLR'] at h
    exact linearBlockStandardPair_of_locImg3' c.hΩ c.hex c.hP1 c.hO3 hL hL' h

theorem rootInv_eq_of_locImg_eq {L L' : Subgroup G} {R R' : Subgroup SL(m + 1, GaloisField 3 1)}
    {i i' : SL(m + 1, GaloisField 3 1)} (hRi : IsLongRootSL2 c.hn R i)
    (hRi' : IsLongRootSL2 c.hn R' i') (hLR : locImg Ω z L = R.map c.d.ψ)
    (hLR' : locImg Ω z L' = R'.map c.d.ψ) (h : locImg Ω z L = locImg Ω z L') : i = i' := by
  have himg : Transfer.IsLongRootImage c.d.ψ c.hn (locImg Ω z L') (c.d.ψ i') :=
    ⟨R', i', hRi', hLR'.symm, rfl⟩
  have hmem : c.d.ψ i ∈ locImg Ω z L' := by
    rw [← h, hLR]
    exact ⟨i, hRi.mem, rfl⟩
  have hord : orderOf (c.d.ψ i) = 2 := by
    have himg0 : Transfer.IsLongRootImage c.d.ψ c.hn (locImg Ω z L) (c.d.ψ i) :=
      ⟨R, i, hRi, hLR.symm, rfl⟩
    exact himg0.orderOf_eq_two odd_gf3 c.hn3 c.d.ker_le
  have h1 := himg.eq_of_orderOf_eq_two odd_gf3 c.hn3 c.d.ker_le hmem hord
  exact Transfer.eq_of_map_eq_of_isLongRootSL2 two_ne_zero_gf3 hRi hRi' c.d.ker_le c.hlift h1

theorem eq_of_rootInv_eq [Finite G] {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) {R R' : Subgroup SL(m + 1, GaloisField 3 1)}
    {i : SL(m + 1, GaloisField 3 1)} (hRi : IsLongRootSL2 c.hn R i)
    (hRi' : IsLongRootSL2 c.hn R' i) (hLR : locImg Ω z L = R.map c.d.ψ)
    (hLR' : locImg Ω z L' = R'.map c.d.ψ) : L = L' := by
  have hRR : R = R' := by
    rw [hRi.eq_longRootGroup two_ne_zero_gf3, hRi'.eq_longRootGroup two_ne_zero_gf3]
  exact locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL hL' (by rw [hLR, hLR', hRR])

theorem ne_of_rootInv [Finite G] {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (hne : L ≠ L')
    {R R' : Subgroup SL(m + 1, GaloisField 3 1)} {i i' : SL(m + 1, GaloisField 3 1)}
    (hRi : IsLongRootSL2 c.hn R i) (hRi' : IsLongRootSL2 c.hn R' i')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) : i ≠ i' := by
  intro h
  subst h
  exact hne (c.eq_of_rootInv_eq hL hL' hRi hRi' hLR hLR')

theorem rel_dichotomy [Finite G] {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) (hL'K : L' ≠ K) (hne : L ≠ L')
    {zL zL' : G} (hzL : IsClassicalMember3 L zL) (hzL' : IsClassicalMember3 L' zL')
    (hcomm : zL * zL' = zL' * zL) :
    Commutes L L' ∨ ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W L L' := by
  obtain ⟨R, i, hRi, hLR, hi⟩ := c.exists_rootData hL hLK hzL
  obtain ⟨R', i', hRi', hLR', hi'⟩ := c.exists_rootData hL' hL'K hzL'
  have hc : Commute (c.d.ψ i) (c.d.ψ i') := by
    show c.d.ψ i * c.d.ψ i' = c.d.ψ i' * c.d.ψ i
    rw [hi, hi']
    have : (⟨zL, le_centralizingLayer hL hzL.mem⟩ : ↥(locLayer Ω z)) *
        ⟨zL', le_centralizingLayer hL' hzL'.mem⟩ =
        ⟨zL', le_centralizingLayer hL' hzL'.mem⟩ * ⟨zL, le_centralizingLayer hL hzL.mem⟩ :=
      Subtype.ext hcomm
    unfold locElt
    rw [← map_mul, ← map_mul, this]
  have hne' : c.d.ψ i ≠ c.d.ψ i' := by
    intro h
    have hii := Transfer.eq_of_map_eq_of_isLongRootSL2 two_ne_zero_gf3 hRi hRi' c.d.ker_le
      c.hlift h
    have hRR : R = R' := by
      rw [hRi.eq_longRootGroup two_ne_zero_gf3, hRi'.eq_longRootGroup two_ne_zero_gf3, hii]
    apply hne
    apply locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL hL'
    rw [hLR, hLR', hRR]
  have h₁ : Transfer.IsLongRootImage c.d.ψ c.hn (locImg Ω z L) (c.d.ψ i) :=
    ⟨R, i, hRi, hLR.symm, rfl⟩
  have h₂ : Transfer.IsLongRootImage c.d.ψ c.hn (locImg Ω z L') (c.d.ψ i') :=
    ⟨R', i', hRi', hLR'.symm, rfl⟩
  rcases lemma_6_5_image3 card_gf3 c.hn3 c.d.ker_le c.hlift h₁ h₂ hc hne' with h | ⟨-, h⟩
  · left
    exact commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 hL hL' h
  · right
    exact linearBlockStandardPair_of_locImg3' c.hΩ c.hex c.hP1 c.hO3 hL hL' h

end ACtx3

end CFSG.ClassicalInvolution.Q3.Q3W
