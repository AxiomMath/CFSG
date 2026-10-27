module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory.WielandtProduct

open Subgroup

variable {G : Type*} [Group G]

theorem exists_orderOf_eq_commute_of_isPGroup [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) (hne : P ≠ ⊥) :
    ∃ z ∈ P, orderOf z = p ∧ ∀ y ∈ P, Commute z y := by
  have : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hne
  have hc : Nontrivial (center P) := hP.center_nontrivial
  have hpc : p ∣ Nat.card (center P) := by
    rcases (hP.to_subgroup (center P)).card_eq_or_dvd with h1 | h1
    · exact absurd (Finite.one_lt_card_iff_nontrivial.mpr hc) (by rw [h1]; exact lt_irrefl 1)
    · exact h1
  have := Fintype.ofFinite (center P)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := center P) p
    (by rwa [← Nat.card_eq_fintype_card])
  refine ⟨((z : P) : G), (z : P).2, ?_, fun y hy => ?_⟩
  · rw [← hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  · have := (mem_center_iff.mp z.2) ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm

theorem exists_mem_commute_of_le_of_isPGroup [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {P N : Subgroup G} (hP : IsPGroup p P) (hNP : N ≤ P) (hPN : P ≤ normalizer (N : Set G))
    (hne : N ≠ ⊥) : ∃ n ∈ N, n ≠ 1 ∧ ∀ y ∈ P, Commute n y := by
  have := hP.isNilpotent
  have hNn : (N.subgroupOf P).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.mp (hPN y.2) x).mp hx
  have hNb : N.subgroupOf P ≠ ⊥ := by
    intro hb
    rw [subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hNP] at hb
    exact hne hb
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hNb
  obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h1
  refine ⟨(((n : P) : P) : G), (mem_subgroupOf.mp (mem_inf.mp n.2).1), ?_, fun y hy => ?_⟩
  · intro h
    apply hn1
    ext
    simpa using h
  · have := (mem_center_iff.mp (mem_inf.mp n.2).2) ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm

theorem le_of_coprime_index {X : Type*} [Group X] [Finite X] {K H : Subgroup X} [K.Normal]
    (hcop : Nat.Coprime (Nat.card H) K.index) : H ≤ K := by
  have h1 : Nat.card (H.map (QuotientGroup.mk' K)) ∣ Nat.card H := Subgroup.card_map_dvd _ _
  have h2 : Nat.card (H.map (QuotientGroup.mk' K)) ∣ K.index :=
    Subgroup.card_subgroup_dvd_card _
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [Subgroup.card_eq_one, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h3
  exact h3

theorem index_dvd_card_of_sup_eq_top {X : Type*} [Group X] [Finite X] {H N : Subgroup X}
    [N.Normal] (h : H ⊔ N = ⊤) : H.index ∣ Nat.card N := by
  have e := Subgroup.relIndex_sup_right H N
  rw [h, Subgroup.relIndex_top_right] at e
  have h1 := H.card_mul_index
  have h2 := N.card_mul_index
  have h3 : N.relIndex H * Nat.card (N.subgroupOf H) = Nat.card H := by
    rw [mul_comm]
    exact (N.subgroupOf H).card_mul_index
  refine ⟨Nat.card (N.subgroupOf H), ?_⟩
  have hpos : 0 < N.relIndex H := by
    rcases Nat.eq_zero_or_pos (N.relIndex H) with h0 | h0
    · rw [h0, zero_mul] at h3
      exact absurd h3.symm Nat.card_pos.ne'
    · exact h0
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc N.relIndex H * Nat.card N = Nat.card N * N.index := by rw [e, mul_comm]
    _ = Nat.card X := h2
    _ = Nat.card H * H.index := h1.symm
    _ = N.relIndex H * Nat.card (N.subgroupOf H) * H.index := by rw [h3]
    _ = N.relIndex H * (H.index * Nat.card (N.subgroupOf H)) := by ring

@[expose] def normalizerConj (V : Subgroup G) : normalizer (V : Set G) →* MulAut V where
  toFun g :=
    { toFun := fun w => ⟨g * w * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 w).mp w.2⟩
      invFun := fun w => ⟨(g : G)⁻¹ * w * g, by
        have := (mem_normalizer_iff.mp (inv_mem g.2) w).mp w.2
        simpa using this⟩
      left_inv := fun w => by ext; simp [mul_assoc]
      right_inv := fun w => by ext; simp [mul_assoc]
      map_mul' := fun w₁ w₂ => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun g₁ g₂ => by ext; simp [mul_assoc, MulAut.mul_apply]

theorem coe_normalizerConj_apply (V : Subgroup G) (g : normalizer (V : Set G)) (w : V) :
    ((normalizerConj V g w : V) : G) = g * w * (g : G)⁻¹ := rfl

end CFSG.GroupTheory.WielandtProduct
