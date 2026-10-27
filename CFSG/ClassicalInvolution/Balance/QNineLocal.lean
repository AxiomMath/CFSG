module

public import CFSG.ClassicalInvolution.Balance.QNineStandard
public import CFSG.ClassicalInvolution.Balance.PassTwoWeak

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

@[expose] def LeviBlockImage (p f : ℕ) [Fact p.Prime] {X : Type} [Group X] (U : Subgroup X) :
    Prop :=
  (∃ V W : Subgroup X, WeakCT.LinearBlockStandardPair (GaloisField p f) W U V) ∨
  (∃ V W : Subgroup X, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W U V) ∨
  SymplecticLongBlockImage (GaloisField p f) U

theorem LeviBlockImage.of_symplecticBlockStandardPair {p f : ℕ} [Fact p.Prime] {X : Type}
    [Group X] {W U V : Subgroup X}
    (h : Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField p f) W U V) :
    LeviBlockImage p f U :=
  Or.inr (Or.inr (symplecticLongBlockImage_of_standardPair h))

theorem LeviBlockImage.congr_exp {p e f : ℕ} [Fact p.Prime] (h : e = f) {X : Type} [Group X]
    {U : Subgroup X} (hU : LeviBlockImage p e U) : LeviBlockImage p f U :=
  h ▸ hU

theorem LeviBlockImage.map {p f : ℕ} [Fact p.Prime] (hq : 5 ≤ p ^ f) {K X : Type} [Group K]
    [Group X] {U : Subgroup K} (h : LeviBlockImage p f U) (ψ : K →* X)
    (hψ : ψ.ker ≤ Subgroup.center K) : LeviBlockImage p f (U.map ψ) := by
  have hf := ne_zero_of_five_le_pow hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  rcases h with ⟨V, W, h⟩ | ⟨V, W, h⟩ | h
  · exact Or.inl ⟨V.map ψ, W.map ψ, linearBlockStandardPair_map_of_ker_le_center h ψ hψ⟩
  · exact Or.inr (Or.inl ⟨V.map ψ, W.map ψ, unitaryBlockStandardPair_map_of_ker_le_center
      (CFSG.LieType.Universal.card_galoisField_two_mul p f (Nat.one_le_iff_ne_zero.mpr hf)) hq
      h ψ hψ⟩)
  · exact Or.inr (Or.inr (symplecticLongBlockImage_map (by rw [hcard]; exact hq) h ψ hψ))

section Modulo

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]

theorem nonempty_equiv_sl2_of_leviBlockImage (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O)) {K : Subgroup Y} (hK : K ≤ ⁅K, K⁆)
    (h : LeviBlockImage p f (K.map (QuotientGroup.mk' O))) :
    Nonempty (K ≃* SL(2, GaloisField p f)) := by
  have hf := ne_zero_of_five_le_pow hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  rcases h with ⟨V, W, h⟩ | ⟨V, W, h⟩ | h
  · exact nonempty_equiv_sl2_of_linearBlockStandardPair hcard hq hOc hOodd hK h
  · exact nonempty_equiv_sl2_of_unitaryBlockStandardPair hp2
      (CFSG.LieType.Universal.card_galoisField_two_mul p f (Nat.one_le_iff_ne_zero.mpr hf)) hq
      hOc hOodd hK h
  · exact nonempty_equiv_sl2_of_symplecticLongBlockImage hp2 hcard hq hOc hOodd hK h

end Modulo

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem classicalInvolutionOddCore_eq_bot_of_leviBlockImage [Finite G] (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (h : LeviBlockImage p f (locImg Ω x L)) :
    classicalInvolutionOddCore L = ⊥ ∧ Nonempty (L ≃* SL(2, GaloisField p f)) := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hzY := hz.subgroupOf p f (le_centralizingLayer hL)
  have hperf : (L.subgroupOf (locLayer Ω x)) ≤
      ⁅L.subgroupOf (locLayer Ω x), L.subgroupOf (locLayer Ω x)⁆ :=
    (commutator_eq_of_isClassicalMember hzY).ge
  obtain ⟨e⟩ := nonempty_equiv_sl2_of_leviBlockImage hp2 hq (O := classicalInvolutionOddCore
    ↥(locLayer Ω x)) hP1 (CFSG.ComponentClassification.OddCore.odd_card _) hperf h
  have eL : L ≃* SL(2, GaloisField p f) :=
    (Subgroup.subgroupOfEquivOfLe (le_centralizingLayer hL)).symm.trans e
  obtain ⟨e'⟩ := hz.nonempty_equiv
  have hbot : classicalInvolutionOddCore L = ⊥ := by
    have : Finite L := inferInstance
    exact oddCore_eq_bot_of_equiv eL e'
  exact ⟨hbot, ⟨eL⟩⟩

theorem exactMembers_of_oddCore_eq_bot {Ω : Set (Subgroup G)}
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {L₀ : Subgroup G} (hL₀ : L₀ ∈ Ω)
    (hO : classicalInvolutionOddCore L₀ = ⊥) : ExactMembers Ω := by
  obtain ⟨K, -, hall⟩ := hsingle
  obtain ⟨g₀, hg₀⟩ := hall L₀ hL₀
  intro L hL
  obtain ⟨g, hg⟩ := hall L hL
  have hK : K = conjSub g₀⁻¹ L₀ := by rw [hg₀, conjSub_inv_conjSub]
  have hLeq : L = conjSub (g * g₀⁻¹) L₀ := by rw [conjSub_mul, ← hK, hg]
  rw [hLeq]
  exact classicalInvolutionOddCore_conjSub_eq_bot hO _

theorem exactMembers_of_leviBlockImage [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (h : LeviBlockImage p f (locImg Ω x L)) : ExactMembers Ω :=
  exactMembers_of_oddCore_eq_bot hsingle hL.1
    (classicalInvolutionOddCore_eq_bot_of_leviBlockImage hp2 hq hΩ hP1 hL h).1

theorem exactMembers_of_linearPair [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    {W V : Subgroup (locQuot Ω x)}
    (h : WeakCT.LinearBlockStandardPair (GaloisField p f) W (locImg Ω x L) V) :
    ExactMembers Ω :=
  exactMembers_of_leviBlockImage hp2 hq hΩ hsingle hP1 hL (Or.inl ⟨V, W, h⟩)

theorem exactMembers_of_unitaryPair [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    {W V : Subgroup (locQuot Ω x)}
    (h : Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (locImg Ω x L) V) :
    ExactMembers Ω :=
  exactMembers_of_leviBlockImage hp2 hq hΩ hsingle hP1 hL (Or.inr (Or.inl ⟨V, W, h⟩))

theorem exactMembers_of_symplecticPair [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    {W V : Subgroup (locQuot Ω x)}
    (h : Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField p f) W (locImg Ω x L)
      V) :
    ExactMembers Ω :=
  exactMembers_of_leviBlockImage hp2 hq hΩ hsingle hP1 hL
    (LeviBlockImage.of_symplecticBlockStandardPair h)

end Local

end CFSG.ClassicalInvolution.Balance
