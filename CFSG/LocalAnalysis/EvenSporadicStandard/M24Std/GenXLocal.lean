module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std.GenX

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G]

structure LS (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G) : Prop where
  order_z : orderOf z = 2
  z_central : zpowers z ≤ centralizer (L : Set G)
  centralizer_eq : centralizer ({z} : Set G) = L ⊔ zpowers z
  disjoint : Disjoint L (zpowers z)
  sporadic : IsSporadic L .M24
  conj_not_mem : ∀ g : G, g * z * g⁻¹ ∉ L
  hom_z : ∀ ψ : G →* ℤˣ, ψ z = 1

theorem LS.of_localSetting {L : Subgroup G} {z : G} (hs : LocalSetting G L z)
    (hGz : ∀ ψ : G →* ℤˣ, ψ z = 1) : LS G L z :=
  ⟨hs.order_z, hs.z_central, hs.centralizer_eq, hs.disjoint, hs.sporadic, hs.conj_not_mem, hGz⟩

namespace LS

variable {L : Subgroup G} {z : G}

theorem mul_self_z (hs : LS G L z) : z * z = 1 := by
  rw [← pow_two, ← hs.order_z, pow_orderOf_eq_one]

theorem z_ne_one (hs : LS G L z) : z ≠ 1 := by
  intro h
  have := hs.order_z
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem eq_one_or_eq_z (hs : LS G L z) {b : G} (hb : b ∈ zpowers z) : b = 1 ∨ b = z := by
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

theorem z_not_mem (hs : LS G L z) : z ∉ L := by
  intro hz
  have : z ∈ L ⊓ zpowers z := ⟨hz, mem_zpowers z⟩
  rw [disjoint_iff.1 hs.disjoint] at this
  exact hs.z_ne_one (mem_bot.1 this)

theorem comm_z (hs : LS G L z) {l : G} (hl : l ∈ L) : l * z = z * l :=
  mem_centralizer_iff.1 (hs.z_central (mem_zpowers z)) l hl

theorem exists_mem_L (hs : LS G L z) {q : G} (hq : q ∈ centralizer ({z} : Set G)) :
    ∃ l ∈ L, q = l ∨ q = l * z := by
  rw [hs.centralizer_eq] at hq
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hs.z_central hq
  rcases hs.eq_one_or_eq_z hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

end LS

theorem card_centralizer_of_localSetting {L : Subgroup G} {z : G}
    (hs : LocalSetting G L z) :
    Nat.card (centralizer ({z} : Set G)) = 2 ^ (10 + 1) * 239085 := by
  have e := mulEquivProdSup hs.z_central hs.disjoint
  obtain ⟨e'⟩ := hs.sporadic
  have hLc : Nat.card L = 244823040 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  rw [hs.centralizer_eq, ← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers,
    hs.order_z, hLc]
  norm_num

end CFSG.EvenSporadicStandard.M24Std.GenX
