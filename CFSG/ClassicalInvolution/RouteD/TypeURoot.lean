module

public import CFSG.ClassicalInvolution.RouteD.TypeULift
public import CFSG.ClassicalInvolution.RouteD.LocalRoot

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

section Local

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem psiU_root_inv [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hm : 2 ≤ m)
    (d : ShapeUDict p f m Ω z) {L : Subgroup G}
    {R : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1))}
    {i : Su (GaloisField p (2 * f)) p f (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField p (2 * f)) p f (by omega : 2 ≤ m + 1) R i)
    (hLR : locImg Ω z L = R.map d.ψ) (hLY : L ≤ locLayer Ω z) {zL : G} (hzL : zL ∈ L)
    (h2 : orderOf zL = 2) : d.ψ i = locElt Ω z zL (hLY hzL) := by
  have hK := typeU_card_field (p := p) (f := f) hq
  have himg : Transfer.IsLongRootSU2Image d.ψ (by omega : 2 ≤ m + 1) (locImg Ω z L) (d.ψ i) :=
    ⟨R, i, hRi, hLR.symm, rfl⟩
  exact (himg.eq_of_orderOf_eq_two hK hp2 hq (by omega) d.ker_le (locElt_mem_locImg hLY hzL)
    (orderOf_locElt (hLY hzL) h2)).symm

structure UCtx (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) where
  hm : 2 ≤ m
  hp2 : p ≠ 2
  hq : 5 ≤ p ^ f
  hΩ : InClass p f Ω
  hex : ExactMembers Ω
  hK : K ∈ Ω
  hz : IsClassicalMember p f K z
  hP1 : LocalOddCentral Ω {z}
  d : ShapeUDict p f m Ω z
  hlift : m + 1 ≠ 4 ∨ Transfer.KerInvolutionFree d.ψ

namespace UCtx

variable (c : UCtx p f m Ω K z)

include c

theorem hf : f ≠ 0 := by
  rintro rfl
  have := c.hq
  simp at this

theorem card_eq : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := typeU_card_field c.hq

theorem h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_of_charP_ne_two c.hp2

theorem hn : 2 ≤ m + 1 := by have := c.hm; omega

theorem hn3 : 3 ≤ m + 1 := by have := c.hm; omega

theorem hF : OddCoverSU3 (GaloisField p (2 * f)) p f := oddCoverSU3 c.hp2 c.card_eq c.hq

theorem isPerfect_of_isLongRootSU2 {R : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1))}
    {i : Su (GaloisField p (2 * f)) p f (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn R i) : Group.IsPerfect ↥R :=
  (hRi.isClassicalSL2 c.card_eq c.hp2).isPerfect (by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield c.card_eq]
    have := c.hq
    omega)

variable [Finite G]

theorem exists_rootData {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K)
    {zL : G} (hzL : IsClassicalMember p f L zL) :
    ∃ (R : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1)))
      (i : Su (GaloisField p (2 * f)) p f (m + 1)),
      IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn R i ∧ locImg Ω z L = R.map c.d.ψ ∧
      c.d.ψ i = locElt Ω z zL (le_centralizingLayer hL hzL.mem) := by
  obtain ⟨R, hR, hLR⟩ := typeU_exists_root_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.d
    hL hLK
  obtain ⟨i, hi⟩ := hR
  exact ⟨R, i, hi, hLR, psiU_root_inv c.hp2 c.hq c.hm c.d hi hLR (le_centralizingLayer hL)
    hzL.mem hzL.orderOf_eq_two⟩

theorem commutes_iff_root {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1))}
    {i : Su (GaloisField p (2 * f)) p f (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn R i)
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact commutes_of_commutes_map c.d.ψ c.d.ker_le (c.isPerfect_of_isLongRootSU2 hRi) h1
  · intro h
    refine commutes_of_commutes_locImg c.hΩ c.hP1 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes _ h

theorem rel_dichotomy {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) (hL'K : L' ≠ K) (hne : L ≠ L')
    {zL zL' : G} (hzL : IsClassicalMember p f L zL) (hzL' : IsClassicalMember p f L' zL')
    (hcomm : zL * zL' = zL' * zL) :
    Commutes L L' ∨ ∃ W : Subgroup G,
      UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W L L' := by
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
    have hii := Transfer.eq_of_map_eq_of_isLongRootSU2 c.card_eq c.hp2 c.hq c.hn3 hRi hRi'
      c.d.ker_le c.hlift h
    have hRR : R = R' := by
      rw [hRi.eq_longRootGroupSU c.h2, hRi'.eq_longRootGroupSU c.h2, hii]
    apply hne
    apply locImg_injOn c.hΩ c.hP1 hL hL'
    rw [hLR, hLR', hRR]
  have h₁ : Transfer.IsLongRootSU2Image c.d.ψ c.hn (locImg Ω z L) (c.d.ψ i) :=
    ⟨R, i, hRi, hLR.symm, rfl⟩
  have h₂ : Transfer.IsLongRootSU2Image c.d.ψ c.hn (locImg Ω z L') (c.d.ψ i') :=
    ⟨R', i', hRi', hLR'.symm, rfl⟩
  rcases Transfer.lemma_6_5_su_image c.card_eq c.hp2 c.hq c.hn3 c.d.ker_le c.hlift h₁ h₂ hc
      hne' with h | ⟨-, h⟩
  · left
    exact commutes_of_commutes_locImg c.hΩ c.hP1 hL hL' h
  · right
    obtain ⟨zz, hzz⟩ := c.hΩ.classical L hL.1
    obtain ⟨zz', hzz'⟩ := c.hΩ.classical L' hL'.1
    exact unitaryBlockStandardPair_of_locImg_perfect c.hq c.card_eq c.hF c.hP1
      (le_centralizingLayer hL) (le_centralizingLayer hL')
      (commutator_eq_of_isClassicalMember hzz).ge (commutator_eq_of_isClassicalMember hzz').ge h

omit [Finite G] in
theorem rootInv_eq_of_locImg_eq {L L' : Subgroup G}
    {R R' : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1))}
    {i i' : Su (GaloisField p (2 * f)) p f (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn R i)
    (hRi' : IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn R' i')
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
    exact himg0.orderOf_eq_two c.card_eq c.hp2 c.hq c.hn3 c.d.ker_le
  have h1 := himg.eq_of_orderOf_eq_two c.card_eq c.hp2 c.hq c.hn3 c.d.ker_le hmem hord
  exact Transfer.eq_of_map_eq_of_isLongRootSU2 c.card_eq c.hp2 c.hq c.hn3 hRi hRi' c.d.ker_le
    c.hlift h1

theorem eq_of_rootInv_eq {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1))}
    {i : Su (GaloisField p (2 * f)) p f (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn R i)
    (hRi' : IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn R' i)
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) : L = L' := by
  have hRR : R = R' := by
    rw [hRi.eq_longRootGroupSU c.h2, hRi'.eq_longRootGroupSU c.h2]
  exact locImg_injOn c.hΩ c.hP1 hL hL' (by rw [hLR, hLR', hRR])

end UCtx

end Local

end CFSG.ClassicalInvolution.RouteD
