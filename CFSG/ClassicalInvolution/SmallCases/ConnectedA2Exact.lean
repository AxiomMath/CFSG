module

public import CFSG.ClassicalInvolution.Balance.QNineLocal
public import CFSG.ClassicalInvolution.Generic.TypeA
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Frame
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Inputs

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped IsMulCommutative MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem exactMembers_of_levi_block {K : Subgroup G} {z : G} (hb : Branch p f K z) {x : G}
    (hP1 : LocalOddCentral (conjClass K) {x}) {L₁ : Subgroup G}
    (hL₁ : L₁ ∈ centralizingMembers (conjClass K) {x})
    (h : LeviBlockImage p f (L₁.subgroupOf (locLayer (conjClass K) x))) :
    ExactMembers (conjClass K) :=
  exactMembers_of_leviBlockImage hb.odd hb.five (inClass_conjugates hb.member)
    (exists_single_class K) hP1 hL₁
    (LeviBlockImage.map hb.five h
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass K) x)))
      (by rw [QuotientGroup.ker_mk']; exact hP1))

omit [Finite G] [IsSimpleGroup G] in
theorem linearBlockStandardPair_sup_of_a2Pair {F : Type} [Field F] {E K L : Subgroup G}
    (h : LinearA2Pair F E K L) : WeakCT.LinearBlockStandardPair F (K ⊔ L) K L := by
  obtain ⟨θ, hker, hK, hL, -, -⟩ := h
  have e : ∀ B : Subgroup SL(3, F),
      B.map (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = B := fun B => by
    rw [inv_one]
    exact conjSub_one B
  refine ⟨θ, 1, ?_, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.Models.B12_sup_B23, Subgroup.map_sup,
      hK, hL]
  · rw [e, hK]
  · rw [e, hL]

theorem exactMembers_of_inputs {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hD : HasDatum p f K) (hP1 : A2P1 p f) : ExactMembers (conjClass K) := by
  have hq := hb.five
  have hp2 := hb.odd
  have hf : 0 < f := pos_of_five_le hq
  have hΩ : InClass p f (conjClass K) := inClass_conjugates hb.member
  obtain ⟨L₁, L₂, t, h₁, h₂, hLD⟩ := id hD
  rcases hLD with hLD | hLD
  · have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
    obtain ⟨A, Fr, hs₁, hs₂, hne, hnc, hpair, -⟩ := hLD.exists_rankFrame
      (CFSG.ClassicalInvolution.Generic.DeltaClosure.odd_card_galoisField hp2 hq)
      (by rw [hF]; exact hq) hΩ.conjInvariant h₁ h₂
    have hcard8 : Nat.card A = 8 :=
      le_antisymm (card_le_eight_of_not_bootData hb.member Fr rfl ⟨L₁, hs₁⟩ hb.noBoot) Fr.card
    have hP1A := hP1 G K z hb hD _ hF A _ Fr hcard8 ⟨L₁, hs₁, L₂, hs₂, hne, hnc⟩
    obtain ⟨x, hx, hx1⟩ := Fr.exists_ne_one_mem_axisSub_inf_axisSub hs₁ hs₂
    obtain ⟨hxL₁, hxL₂⟩ := Subgroup.mem_inf.mp hx
    have hL₁ : L₁ ∈ centralizingMembers (conjClass K) {x} :=
      ⟨h₁, fun k hk => by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact ((mem_axisSub_iff.mp hxL₁).2 k hk).symm⟩
    have hL₂ : L₂ ∈ centralizingMembers (conjClass K) {x} :=
      ⟨h₂, fun k hk => by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact ((mem_axisSub_iff.mp hxL₂).2 k hk).symm⟩
    have hW : L₁ ⊔ L₂ ≤ locLayer (conjClass K) x :=
      sup_le (le_centralizingLayer hL₁) (le_centralizingLayer hL₂)
    exact exactMembers_of_levi_block hb (hP1A x (mem_axisSub_iff.mp hxL₁).1 hx1) hL₁
      (Or.inl ⟨L₂.subgroupOf _, (L₁ ⊔ L₂).subgroupOf _,
        linearBlockStandardPair_subgroupOf hW (linearBlockStandardPair_sup_of_a2Pair hpair)⟩)
  · have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
      rw [GaloisField.card p (2 * f) (by omega), pow_mul']
    obtain ⟨A, Fr, hs₁, hs₂, hne, hnc, hpair, -⟩ :=
      hLD.exists_rankFrame hK hp2 hq hΩ.conjInvariant h₁ h₂
    have hF := CFSG.LieType.Steinberg.card_fixedSubfield hK
    have hcard8 : Nat.card A = 8 :=
      le_antisymm (card_le_eight_of_not_bootData hb.member Fr rfl ⟨L₁, hs₁⟩ hb.noBoot) Fr.card
    have hP1A := hP1 G K z hb hD _ hF A _ Fr hcard8 ⟨L₁, hs₁, L₂, hs₂, hne, hnc⟩
    obtain ⟨x, hx, hx1⟩ := Fr.exists_ne_one_mem_axisSub_inf_axisSub hs₁ hs₂
    obtain ⟨hxL₁, hxL₂⟩ := Subgroup.mem_inf.mp hx
    have hL₁ : L₁ ∈ centralizingMembers (conjClass K) {x} :=
      ⟨h₁, fun k hk => by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact ((mem_axisSub_iff.mp hxL₁).2 k hk).symm⟩
    have hL₂ : L₂ ∈ centralizingMembers (conjClass K) {x} :=
      ⟨h₂, fun k hk => by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact ((mem_axisSub_iff.mp hxL₂).2 k hk).symm⟩
    have hW : L₁ ⊔ L₂ ≤ locLayer (conjClass K) x :=
      sup_le (le_centralizingLayer hL₁) (le_centralizingLayer hL₂)
    have hq2 : p ^ f ≠ 2 := by omega
    exact exactMembers_of_levi_block hb (hP1A x (mem_axisSub_iff.mp hxL₁).1 hx1) hL₁
      (Or.inr (Or.inl ⟨L₂.subgroupOf _, (L₁ ⊔ L₂).subgroupOf _,
        unitaryBlockStandardPair_subgroupOf hW
          (unitaryBlockStandardPair_sup_of_a2Pair hK hq2 hpair)⟩))

end CFSG.ClassicalInvolution.ConnectedA2
