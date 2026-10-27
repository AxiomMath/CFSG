module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LocalG
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure Setting (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  order_z : orderOf z = 2
  z_central : zpowers z ≤ centralizer (L : Set G)
  centralizer_eq : centralizer ({z} : Set G) = L ⊔ zpowers z
  disjoint : Disjoint L (zpowers z)
  sporadic : IsSporadic L .M24

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem setting_of_stdHyp
    (h : StdHyp G L) (hL : IsSporadic L .M24) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) : Setting G L t := by
  have := h.simple
  have hS := fun S => card_sylow_eq_two_of_M24 h hL S
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_M24 hL
  have hq : IsSporadic (L ⧸ center L) .M24 := isSporadic_quotient_of_center_eq_bot hZ hL
  have hinn : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q :=
    HypOne.M24.allInner_of_isSporadic hq
  obtain ⟨hC, hd, hle⟩ := h.centralizer_eq_prod_of_center_eq_bot hS ht ht2
    (h.centralizer_le_sup_centralizer_of_inner ht ht2 hinn) hZ
  exact ⟨h.simple, h.nonabelian, ht2, hle, hC, hd, hL⟩

namespace Setting

variable {z : G}

theorem mul_self_z (hs : Setting G L z) : z * z = 1 := by
  rw [← pow_two, ← hs.order_z, pow_orderOf_eq_one]

theorem z_ne_one (hs : Setting G L z) : z ≠ 1 := by
  intro h
  have := hs.order_z
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem eq_one_or_eq_z (hs : Setting G L z) {b : G} (hb : b ∈ zpowers z) : b = 1 ∨ b = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h := zpow_mod_orderOf z k
  rw [hs.order_z] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h]
    simp [h0]
  · right
    rw [← h]
    simp [h1]

theorem z_not_mem (hs : Setting G L z) : z ∉ L := by
  intro hz
  have : z ∈ L ⊓ zpowers z := ⟨hz, mem_zpowers z⟩
  rw [disjoint_iff.1 hs.disjoint] at this
  exact hs.z_ne_one (mem_bot.1 this)

theorem comm_z (hs : Setting G L z) {l : G} (hl : l ∈ L) : l * z = z * l :=
  mem_centralizer_iff.1 (hs.z_central (mem_zpowers z)) l hl

theorem exists_mem_L (hs : Setting G L z) {q : G} (hq : q ∈ centralizer ({z} : Set G)) :
    ∃ l ∈ L, q = l ∨ q = l * z := by
  rw [hs.centralizer_eq] at hq
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hs.z_central hq
  rcases hs.eq_one_or_eq_z hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

theorem conj_not_mem
    (hs : Setting G L z) (g : G) : g * z * g⁻¹ ∉ L := by
  intro hg
  have hy1 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hs.mul_self_z]; group
  have hy2 : orderOf (g * z * g⁻¹) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [pow_two]; exact hy1) ?_
    intro h
    apply hs.z_ne_one
    have : g * z * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
    simpa using this
  obtain ⟨v, hvL, hvv⟩ := exists_mul_self_eq_of_mem hs.sporadic hg hy2
  set w : G := g⁻¹ * v * g with hw
  have hww : w * w = z := by
    calc w * w = g⁻¹ * (v * v) * g := by simp only [hw]; group
      _ = z := by rw [hvv]; group
  have hwc : w ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc w * z = w * (w * w) := by rw [hww]
      _ = (w * w) * w := by group
      _ = z * w := by rw [hww]
  obtain ⟨l, hl, hwl | hwl⟩ := hs.exists_mem_L hwc
  · apply hs.z_not_mem
    rw [← hww, hwl]
    exact L.mul_mem hl hl
  · apply hs.z_not_mem
    have : z = l * l := by
      calc z = w * w := hww.symm
        _ = (l * z) * (l * z) := by rw [hwl]
        _ = l * l * (z * z) := by
          rw [mul_assoc, ← mul_assoc z l z, ← hs.comm_z hl]
          group
        _ = l * l := by rw [hs.mul_self_z, mul_one]
    rw [this]
    exact L.mul_mem hl hl

end Setting

omit [Finite G] in
theorem eq_one_or_eq_of_mul_self {x b : G} (hx : x * x = 1) (hb : b ∈ zpowers x) :
    b = 1 ∨ b = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  have h := zpow_mod_orderOf x k
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h2'
  · left
    rw [orderOf_eq_one_iff.1 h1]
    simp
  · rw [h2'] at h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← h]
      simp [h0]
    · right
      rw [← h]
      simp [h1]

theorem exists_sylow_ge {A : Subgroup G} (hAL : A ≤ L) (hAp : IsPGroup 2 A) :
    ∃ U : Subgroup G, A ≤ U ∧ U ≤ L ∧ IsPGroup 2 U ∧ ¬ 2 ∣ (U.subgroupOf L).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp' : IsPGroup 2 (A.subgroupOf L) := hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAL).symm
  obtain ⟨Q, hQ⟩ := hAp'.exists_le_sylow
  refine ⟨(Q : Subgroup L).map L.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hAL hx⟩, hQ hx, rfl⟩
  · exact Q.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective)
  · have : ((Q : Subgroup L).map L.subtype).subgroupOf L = Q := by
      rw [Subgroup.subgroupOf]
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [this]
    exact Sylow.not_dvd_index Q

end CFSG.EvenSporadicStandard.M24Std
