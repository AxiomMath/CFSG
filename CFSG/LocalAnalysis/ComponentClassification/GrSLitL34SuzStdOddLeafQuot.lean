module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSQuot

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

open scoped commutatorElement

variable {C Y : Type*} [Group C] [Group Y] [Finite C] {φ : C →* Y} {D : Subgroup Y}

theorem Quot2Data.map_eq_of_map_le (h : Quot2Data φ D) {K : Subgroup C} (hle : K.map φ ≤ D)
    (hc : Nat.card K = Nat.card D) : K.map φ = D := by
  have := h.finite
  have := h.simple
  have : Finite (K.map φ) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
  set H' : Subgroup D := (K.map φ).subgroupOf D with hH'
  have hcard := card_eq_card_map_mul_card_ker φ K
  have hH'card : Nat.card H' = Nat.card (K.map φ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hidx := Subgroup.card_eq_card_quotient_mul_card_subgroup H'
  have hq : Nat.card (D ⧸ H') = Nat.card (φ.ker.subgroupOf K) := by
    have hpos : 0 < Nat.card (K.map φ) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (D ⧸ H') * Nat.card (K.map φ) = Nat.card D := by rw [← hH'card, ← hidx]
      _ = Nat.card K := hc.symm
      _ = Nat.card (K.map φ) * Nat.card (φ.ker.subgroupOf K) := hcard
      _ = Nat.card (φ.ker.subgroupOf K) * Nat.card (K.map φ) := mul_comm _ _
  have hle_n : Nat.card (D ⧸ H') ≤ Nat.card φ.ker := hq ▸ card_ker_subgroupOf_le φ K
  have hH'top : H' = ⊤ := by
    rw [eq_top_iff]
    intro s _
    have h1 := simple_action_trivial (S := D) (Ω := D ⧸ H') h.big hle_n s ((1 : D) : D ⧸ H')
    have h2 : ((s * 1 : D) : D ⧸ H') = ((1 : D) : D ⧸ H') := h1
    rw [QuotientGroup.eq] at h2
    simpa using h2
  refine le_antisymm hle fun d hd => ?_
  have : (⟨d, hd⟩ : D) ∈ H' := hH'top ▸ Subgroup.mem_top _
  exact this

theorem Quot2Data.isPerfect_commutator (h : Quot2Data φ D)
    (h2 : Nat.card φ.range = Nat.card D * 2) {H : Subgroup C}
    (hc : Nat.card ↥⁅H, H⁆ = Nat.card D) : Group.IsPerfect ↥⁅H, H⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite φ.range :=
    Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have : Finite D := h.finite
  have := h.normal_subgroupOf
  have hDcard : Nat.card (D.subgroupOf φ.range) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.D_le).toEquiv
  have hQcard : Nat.card (φ.range ⧸ D.subgroupOf φ.range) = 2 := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf φ.range)
    rw [hDcard, h2] at hq
    have hpos : 0 < Nat.card D := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (hq.symm.trans (mul_comm _ _))
  have : IsCyclic (φ.range ⧸ D.subgroupOf φ.range) := isCyclic_of_prime_card hQcard
  have : IsMulCommutative (φ.range ⧸ D.subgroupOf φ.range) := IsCyclic.isMulCommutative
  have hcomm : ⁅φ.range, φ.range⁆ ≤ D := by
    have h1 : commutator ↥φ.range ≤ D.subgroupOf φ.range :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    have h2' : (commutator ↥φ.range).map (φ.range).subtype ≤
        (D.subgroupOf φ.range).map (φ.range).subtype := Subgroup.map_mono h1
    rw [map_commutator_eq, Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le h.D_le] at h2'
    exact h2'
  have hle : ⁅H, H⁆.map φ ≤ D := by
    rw [Subgroup.map_commutator]
    exact (Subgroup.commutator_mono (Subgroup.map_le_range φ H)
      (Subgroup.map_le_range φ H)).trans hcomm
  have hmapHeq : ⁅H, H⁆.map φ = D := h.map_eq_of_map_le hle hc
  have hker : φ.ker.subgroupOf ⁅H, H⁆ = ⊥ := by
    have hcard := card_eq_card_map_mul_card_ker φ ⁅H, H⁆
    rw [hmapHeq, hc] at hcard
    refine Subgroup.card_eq_one.1 ?_
    have hpos : 0 < Nat.card D := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hcard)).symm
  let f : ↥⁅H, H⁆ →* D := (φ.domRestrict ⁅H, H⁆).codRestrict D
    (fun x => hle ⟨x, x.2, rfl⟩)
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h1 : φ (a : C) = φ (b : C) := congrArg Subtype.val hab
    have h2 : ((a : C)⁻¹ * (b : C)) ∈ ⁅H, H⁆ :=
      ⁅H, H⁆.mul_mem (⁅H, H⁆.inv_mem a.2) b.2
    have h3 : φ ((a : C)⁻¹ * (b : C)) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h4 : (⟨(a : C)⁻¹ * (b : C), h2⟩ : ↥⁅H, H⁆) = 1 := by
      have h5 : (⟨(a : C)⁻¹ * (b : C), h2⟩ : ↥⁅H, H⁆) ∈ φ.ker.subgroupOf ⁅H, H⁆ :=
        Subgroup.mem_subgroupOf.2 h3
      rw [hker] at h5
      simpa using h5
    exact Subtype.ext (inv_mul_eq_one.1 (congrArg Subtype.val h4))
  have hf_surj : Function.Surjective f := by
    intro d
    have hd : (d : Y) ∈ ⁅H, H⁆.map φ := by
      rw [hmapHeq]
      exact d.2
    obtain ⟨c, hcK, hcd⟩ := hd
    exact ⟨⟨c, hcK⟩, Subtype.ext hcd⟩
  let e : ↥⁅H, H⁆ ≃* D := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hDperf : Group.IsPerfect D := by
    have := h.simple
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator D) with hb | ht
    · exfalso
      obtain ⟨a, b, hab⟩ := h.noncomm
      have hmem : ⁅a, b⁆ ∈ commutator D := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hb, Subgroup.mem_bot] at hmem
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp hmem)
    · exact ht
  have : Group.IsPerfect D := hDperf
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

end CFSG.EvenSporadicStandard.Solomon78
