module

public import CFSG.ClassicalInvolution.RouteD.LocalMembers
public import CFSG.ClassicalInvolution.RouteD.LocalLift

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

section Involutions

variable {Y : Type} [Group Y] [Finite Y]

theorem commute_of_involutions_of_mk (hO : classicalInvolutionOddCore Y ≤ Subgroup.center Y)
    {a b : Y} (ha : a * a = 1) (hb : b * b = 1)
    (h : Commute (QuotientGroup.mk' (classicalInvolutionOddCore Y) a)
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) b)) : Commute a b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  set c : Y := a * b * a⁻¹ * b⁻¹ with hc
  have hcO : c ∈ classicalInvolutionOddCore Y := by
    rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore Y)]
    change QuotientGroup.mk' (classicalInvolutionOddCore Y) c = 1
    simp only [hc, map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h.eq
  have hcen : a * c = c * a := Subgroup.mem_center_iff.mp (hO hcO) a
  have h1 : a * c * a⁻¹ = c⁻¹ := by
    calc a * c * a⁻¹ = a * a * b * a⁻¹ * b⁻¹ * a⁻¹ := by rw [hc]; group
      _ = (a * a) * b * a * b * a := by rw [ha', hb']
      _ = b * a * b * a := by rw [ha, one_mul]
      _ = b * a * b⁻¹ * a⁻¹ := by rw [ha', hb']
      _ = c⁻¹ := by rw [hc]; group
  have h2 : a * c * a⁻¹ = c := by rw [hcen, mul_inv_cancel_right]
  have hcc : c * c = 1 := by
    have : c = c⁻¹ := h2.symm.trans h1
    calc c * c = c * c⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel c
  have hord2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcc)
  have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
  have hdvd : orderOf (⟨c, hcO⟩ : classicalInvolutionOddCore Y) ∣
      Nat.card (classicalInvolutionOddCore Y) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  have hc1 : c = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  exact (commutatorElement_eq_one_iff_mul_comm (g₁ := a) (g₂ := b)).mp hc1

end Involutions

section Commutes

theorem commutes_map_of_commutes {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    {A B : Subgroup X} (h : Commutes A B) : Commutes (A.map φ) (B.map φ) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, h x hx y hy]

end Commutes


section Local

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def locElt (Ω : Set (Subgroup G)) (x y : G) (hy : y ∈ locLayer Ω x) : locQuot Ω x :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨y, hy⟩

theorem locElt_mem_locImg {Ω : Set (Subgroup G)} {x : G} {L : Subgroup G} (hL : L ≤ locLayer Ω x)
    {y : G} (hy : y ∈ L) : locElt Ω x y (hL hy) ∈ locImg Ω x L :=
  ⟨⟨y, hL hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem locElt_mul {Ω : Set (Subgroup G)} {x y y' : G} (hy : y ∈ locLayer Ω x)
    (hy' : y' ∈ locLayer Ω x) :
    locElt Ω x y hy * locElt Ω x y' hy' = locElt Ω x (y * y') ((locLayer Ω x).mul_mem hy hy') := by
  simp only [locElt, ← map_mul]
  rfl

theorem orderOf_locElt [Finite G] {Ω : Set (Subgroup G)} {x y : G} (hy : y ∈ locLayer Ω x)
    (h2 : orderOf y = 2) : orderOf (locElt Ω x y hy) = 2 := by
  have hsq : locElt Ω x y hy ^ 2 = 1 := by
    rw [locElt, ← map_pow]
    have : (⟨y, hy⟩ : ↥(locLayer Ω x)) ^ 2 = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one y
      rwa [h2] at this
    rw [this, map_one]
  have hne : locElt Ω x y hy ≠ 1 := by
    intro h1
    have hO : (⟨y, hy⟩ : ↥(locLayer Ω x)) ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h3 := orderOf_dvd_natCard (⟨⟨y, hy⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
    have h4 : orderOf (⟨⟨y, hy⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]; exact h2
    rw [h4] at h3
    exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card
      (↥(locLayer Ω x)))) (even_iff_two_dvd.mpr h3)
  exact orderOf_eq_prime hsq hne

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem psi_root_inv [Finite G] (hm : 2 ≤ m) (hodd : Odd (Nat.card (GaloisField p f)))
    (d : ShapeADict p f m Ω z) {L : Subgroup G} {R : Subgroup SL(m + 1, GaloisField p f)}
    {i : SL(m + 1, GaloisField p f)} (hRi : IsLongRootSL2 (by omega : 2 ≤ m + 1) R i)
    (hLR : locImg Ω z L = R.map d.ψ) (hLY : L ≤ locLayer Ω z) {zL : G} (hzL : zL ∈ L)
    (h2 : orderOf zL = 2) : d.ψ i = locElt Ω z zL (hLY hzL) := by
  have himg : Transfer.IsLongRootImage d.ψ (by omega : 2 ≤ m + 1) (locImg Ω z L) (d.ψ i) :=
    ⟨R, i, hRi, hLR.symm, rfl⟩
  exact (himg.eq_of_orderOf_eq_two hodd (by omega) d.ker_le (locElt_mem_locImg hLY hzL)
    (orderOf_locElt (hLY hzL) h2)).symm

structure ACtx (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) where
  hm : 2 ≤ m
  hp2 : p ≠ 2
  hq : 5 ≤ p ^ f
  hΩ : InClass p f Ω
  hex : ExactMembers Ω
  hK : K ∈ Ω
  hz : IsClassicalMember p f K z
  hP1 : LocalOddCentral Ω {z}
  d : ShapeADict p f m Ω z
  hF : OddCoverSL3 (GaloisField p f)
  hlift : m + 1 ≠ 4 ∨ Transfer.KerInvolutionFree d.ψ

namespace ACtx

variable (c : ACtx p f m Ω K z)

include c

theorem hf : f ≠ 0 := by
  rintro rfl
  have := c.hq
  simp at this

theorem card_eq : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f c.hf

theorem hodd : Odd (Nat.card (GaloisField p f)) := by
  rw [c.card_eq]
  exact (Nat.Prime.odd_of_ne_two Fact.out c.hp2).pow

theorem h5 : 5 ≤ Nat.card (GaloisField p f) := by rw [c.card_eq]; exact c.hq

theorem h4 : 4 ≤ Nat.card (GaloisField p f) := by have := c.h5; omega

theorem two_ne_zero : (2 : GaloisField p f) ≠ 0 := two_ne_zero_of_odd_natCard c.hodd

theorem hn : 2 ≤ m + 1 := by have := c.hm; omega

theorem hn3 : 3 ≤ m + 1 := by have := c.hm; omega

theorem isPerfect_of_isLongRootSL2 {R : Subgroup SL(m + 1, GaloisField p f)}
    {i : SL(m + 1, GaloisField p f)} (hRi : IsLongRootSL2 c.hn R i) : Group.IsPerfect ↥R :=
  (hRi.isClassicalSL2 c.two_ne_zero).isPerfect c.h4

variable [Finite G]

theorem exists_rootData {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K)
    {zL : G} (hzL : IsClassicalMember p f L zL) :
    ∃ (R : Subgroup SL(m + 1, GaloisField p f)) (i : SL(m + 1, GaloisField p f)),
      IsLongRootSL2 c.hn R i ∧ locImg Ω z L = R.map c.d.ψ ∧
      c.d.ψ i = locElt Ω z zL (le_centralizingLayer hL hzL.mem) := by
  obtain ⟨R, hR, hLR⟩ := exists_root_of_ne c.hm c.hodd c.hΩ c.hex c.hK c.hz c.hP1 c.d hL hLK
  obtain ⟨i, hi⟩ := hR
  exact ⟨R, i, hi, hLR, psi_root_inv c.hm c.hodd c.d hi hLR (le_centralizingLayer hL) hzL.mem
    hzL.orderOf_eq_two⟩

theorem commutes_iff_root {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) {R R' : Subgroup SL(m + 1, GaloisField p f)}
    {i : SL(m + 1, GaloisField p f)} (hRi : IsLongRootSL2 c.hn R i)
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact commutes_of_commutes_map c.d.ψ c.d.ker_le (c.isPerfect_of_isLongRootSL2 hRi) h1
  · intro h
    refine commutes_of_commutes_locImg c.hΩ c.hP1 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes _ h

theorem rel_dichotomy {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) (hL'K : L' ≠ K) (hne : L ≠ L')
    {zL zL' : G} (hzL : IsClassicalMember p f L zL) (hzL' : IsClassicalMember p f L' zL')
    (hcomm : zL * zL' = zL' * zL) :
    Commutes L L' ∨ ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W L L' := by
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
    have hii := Transfer.eq_of_map_eq_of_isLongRootSL2 c.two_ne_zero hRi hRi' c.d.ker_le c.hlift h
    have hRR : R = R' := by
      rw [hRi.eq_longRootGroup c.two_ne_zero, hRi'.eq_longRootGroup c.two_ne_zero, hii]
    apply hne
    apply locImg_injOn c.hΩ c.hP1 hL hL'
    rw [hLR, hLR', hRR]
  have h₁ : Transfer.IsLongRootImage c.d.ψ c.hn (locImg Ω z L) (c.d.ψ i) :=
    ⟨R, i, hRi, hLR.symm, rfl⟩
  have h₂ : Transfer.IsLongRootImage c.d.ψ c.hn (locImg Ω z L') (c.d.ψ i') :=
    ⟨R', i', hRi', hLR'.symm, rfl⟩
  rcases Transfer.lemma_6_5_image c.hodd c.h5 c.hn3 c.d.ker_le c.hlift h₁ h₂ hc hne' with h | ⟨-, h⟩
  · left
    exact commutes_of_commutes_locImg c.hΩ c.hP1 hL hL' h
  · right
    exact linearBlockStandardPair_of_locImg (by have := c.hq; omega) c.hF c.hΩ c.hP1 hL hL' h

omit [Finite G] in
theorem rootInv_eq_of_locImg_eq {L L' : Subgroup G} {R R' : Subgroup SL(m + 1, GaloisField p f)}
    {i i' : SL(m + 1, GaloisField p f)} (hRi : IsLongRootSL2 c.hn R i)
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
    exact himg0.orderOf_eq_two c.hodd c.hn3 c.d.ker_le
  have h1 := himg.eq_of_orderOf_eq_two c.hodd c.hn3 c.d.ker_le hmem hord
  exact Transfer.eq_of_map_eq_of_isLongRootSL2 c.two_ne_zero hRi hRi' c.d.ker_le c.hlift h1

theorem eq_of_rootInv_eq {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) {R R' : Subgroup SL(m + 1, GaloisField p f)}
    {i : SL(m + 1, GaloisField p f)} (hRi : IsLongRootSL2 c.hn R i)
    (hRi' : IsLongRootSL2 c.hn R' i) (hLR : locImg Ω z L = R.map c.d.ψ)
    (hLR' : locImg Ω z L' = R'.map c.d.ψ) : L = L' := by
  have hRR : R = R' := by
    rw [hRi.eq_longRootGroup c.two_ne_zero, hRi'.eq_longRootGroup c.two_ne_zero]
  exact locImg_injOn c.hΩ c.hP1 hL hL' (by rw [hLR, hLR', hRR])

end ACtx

end Local

section Conj

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem IsClassicalMember.conj {L : Subgroup G} {z : G} (h : IsClassicalMember p f L z) (g : G) :
    IsClassicalMember p f (conjSub g L) (g * z * g⁻¹) := by
  have e : L ≃* conjSub g L := Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  refine ⟨?_, conj_mem_conjSub h.mem, ?_, ?_, ?_⟩
  · rw [← h.orderOf_eq_two]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
  · have := h.perfect
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · exact isSubnormal_map_conj_centralizer h.subnormal g
  · obtain ⟨e'⟩ := h.nonempty_equiv
    have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (conjSub g L) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

theorem conjSub_inv_mem_centralizingMembers {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {z g : G} {N M : Subgroup G} (hN : N ∈ Ω) (hw : g * z * g⁻¹ ∈ M) (hc : Commutes N M) :
    conjSub g⁻¹ N ∈ centralizingMembers Ω {z} := by
  have hmem : N ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    ⟨hN, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hc y hy _ hw)⟩
  rw [centralizingMembers_conj hΩ] at hmem
  obtain ⟨N₀, hN₀, rfl⟩ := hmem
  rwa [conjSub_inv_conjSub]

end Conj

end CFSG.ClassicalInvolution.RouteD
