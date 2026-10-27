module

public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}

theorem Ctx17.cen_le (h : Ctx17 G z k S M) : Cen z ≤ M := h.mem.2

theorem Ctx17.ne_top (h : Ctx17 G z k S M) : M ≠ ⊤ := h.mem.1.1

theorem Ctx17.S_le (h : Ctx17 G z k S M) : S ≤ M := h.ctx.S_le_Cen.trans h.cen_le

theorem Ctx17.sylow (h : Ctx17 G z k S M) : CFSG.ABGLocalTools.IsSylowOf 2 S M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.ctx.sylow_top.of_le h.S_le le_top

end Ctx

theorem exists_orderOf_two {H : Type} [Group H] [Finite H] (hH : IsPGroup 2 H) [Nontrivial H] :
    ∃ x : H, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := H)
    have h1 : Nat.card H = 1 := by simpa using hn
    exact (not_nontrivial_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp h1).1) inferInstance
  have h2 : 2 ∣ Nat.card H := by rw [hn]; exact dvd_pow_self 2 hn0
  exact exists_prime_orderOf_dvd_card' 2 h2

theorem exists_involution_center_inf {G : Type} [Group G] [Finite G] {S N : Subgroup G}
    (hS : IsPGroup 2 S) (hN : ∀ s ∈ S, ∀ x ∈ N, s * x * s⁻¹ ∈ N) (hne : S ⊓ N ≠ ⊥) :
    ∃ w ∈ S ⊓ N, (∀ s ∈ S, s * w = w * s) ∧ orderOf w = 2 := by
  have : Group.IsNilpotent S := hS.isNilpotent
  let T : Subgroup S := (S ⊓ N).subgroupOf S
  have hTn : T.Normal := ⟨fun x hx g => by
    have hx' : (x : G) ∈ S ⊓ N := hx
    refine mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact S.mul_mem (S.mul_mem g.2 x.2) (S.inv_mem g.2)
    · exact hN g g.2 x hx'.2⟩
  have hTne : T ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : S) ∈ T := mem_subgroupOf.mpr hx
    rw [h, mem_bot] at hx'
    have : x = 1 := by simpa using congrArg Subtype.val hx'
    simp [this]
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hTne
  have hXp : IsPGroup 2 ↥(T ⊓ center S) := hS.to_subgroup _
  have : Nontrivial ↥(T ⊓ center S) := (Subgroup.nontrivial_iff_ne_bot _).mpr hX
  obtain ⟨x, hx2⟩ := exists_orderOf_two hXp
  have hx : (x : S) ∈ T ⊓ center S := x.2
  have hx' : ((x : S) : G) ∈ S ⊓ N := mem_subgroupOf.mp hx.1
  refine ⟨((x : S) : G), hx', fun s hs => ?_, ?_⟩
  · have := congrArg Subtype.val (mem_center_iff.mp hx.2 ⟨s, hs⟩)
    simpa using this
  · have h1 : orderOf ((x : S) : G) = orderOf (x : S) := Subgroup.orderOf_coe (x : S)
    have h2 : orderOf ((x : ↥(T ⊓ center S)) : S) = orderOf x := Subgroup.orderOf_coe x
    rw [h1, h2]
    exact hx2

theorem mem_of_even_normal {G : Type} [Group G] [Finite G] {S M N : Subgroup G} {z : G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S M) (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set G))
    (hev : Even (Nat.card ↥N))
    (hz : ∀ w ∈ S, (∀ s ∈ S, s * w = w * s) → orderOf w = 2 → w = z) : z ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := hS.inf_of_le_normalizer hNM hMN
  have hcard := hSyl.card_eq
  have hne : S ⊓ N ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    have h2 : 2 ∣ Nat.card ↥N := even_iff_two_dvd.mp hev
    have hpos : 0 < (Nat.card ↥N).factorization 2 :=
      Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' h2
    have : 1 < 2 ^ (Nat.card ↥N).factorization 2 := Nat.one_lt_two_pow hpos.ne'
    omega
  have hN : ∀ s ∈ S, ∀ x ∈ N, s * x * s⁻¹ ∈ N := fun s hs x hx =>
    (mem_normalizer_iff.mp (hMN (hS.le hs)) x).mp hx
  obtain ⟨w, hw, hwc, hw2⟩ := exists_involution_center_inf hS.isPGroup hN hne
  rw [← hz w hw.1 hwc hw2]
  exact hw.2

theorem le_normalizer_map_subtype {G : Type} [Group G] (M : Subgroup G) (K : Subgroup M) [K.Normal] :
    M ≤ normalizer ((K.map M.subtype : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, Normal.conj_mem ‹K.Normal› y hy _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨m, hm⟩⁻¹ * y * ⟨m, hm⟩⁻¹⁻¹, Normal.conj_mem ‹K.Normal› y hy _, ?_⟩
    have h1 : (y : G) = m * x * m⁻¹ := hyx
    show (m⁻¹ * (y : G) * m⁻¹⁻¹ : G) = x
    rw [h1]
    group

section Eqs

variable {G : Type} [Group G]

theorem Fs_eq (M : Subgroup G) : Fs M = (generalizedFitting ↥M).map M.subtype := rfl

theorem Em_eq (M : Subgroup G) : Em M = (layer ↥M).map M.subtype := rfl

theorem Op_eq (p : ℕ) (M : Subgroup G) : Op p M = (pCore p ↥M).map M.subtype := rfl

theorem Fm_eq (M : Subgroup G) : Fm M = (fittingSubgroup ↥M).map M.subtype := rfl

end Eqs

section Ctx2

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}

theorem Ctx17.z_mem_Fs (h : Ctx17 G z k S M) : z ∈ Fs M := by
  have hnorm : (generalizedFitting ↥M).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  rw [Fs_eq]
  refine mem_of_even_normal h.sylow (Subgroup.map_subtype_le _) (le_normalizer_map_subtype M _) ?_
    h.ctx.data.base.zcen
  have : Nat.card ↥((generalizedFitting ↥M).map M.subtype) = Nat.card ↥(generalizedFitting ↥M) :=
    Subgroup.card_map_of_injective M.subtype_injective
  exact this ▸ h.even

end Ctx2

end CFSG.GH74.GLS.Stage2.Final.Thm4
