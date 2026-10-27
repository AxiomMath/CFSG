module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureOddIndex

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

structure Setting (G : Type) [Group G] [Finite G] where
  z : G
  L : Subgroup G
  M : Subgroup G
  E : Subgroup G
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  order_z : orderOf z = 2
  E_le : E ≤ L
  card_E : Nat.card E = 8
  sq_E : ∀ x ∈ E, x * x = 1
  sylow_E : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P →
    ∃ g ∈ L, P ≤ E.map (MulAut.conj g).toMonoidHom
  centralizer_E : centralizer (E : Set G) ⊓ L = E
  card_normalizer_E : Nat.card (normalizer (E : Set G) ⊓ L : Subgroup G) = 168
  L_le : L ≤ M
  L_normal : (L.subgroupOf M).Normal
  odd_relIndex : Odd (L.relIndex M)
  centralizer_eq : centralizer ({z} : Set G) = M ⊔ zpowers z
  disjoint : Disjoint M (zpowers z)

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

@[expose] def V : Subgroup G := H.E ⊔ zpowers H.z

theorem z_mul_self : H.z * H.z = 1 := by
  rw [← pow_two, ← H.order_z, pow_orderOf_eq_one]

theorem z_ne_one : H.z ≠ 1 := by
  intro h
  have := H.order_z
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem E_le_M : H.E ≤ H.M := H.E_le.trans H.L_le

theorem comm_z {l : G} (hl : l ∈ H.M) : l * H.z = H.z * l := by
  have h : l ∈ centralizer ({H.z} : Set G) := H.centralizer_eq ▸ mem_sup_left hl
  exact mem_centralizer_singleton_iff.1 h

theorem comm_z_L {l : G} (hl : l ∈ H.L) : l * H.z = H.z * l := H.comm_z (H.L_le hl)

theorem z_not_mem_M : H.z ∉ H.M := by
  intro h
  have := H.disjoint.le_bot ⟨h, mem_zpowers _⟩
  exact H.z_ne_one (mem_bot.1 this)

theorem mem_centralizer_iff {x : G} :
    x ∈ centralizer ({H.z} : Set G) ↔ x ∈ H.M ∨ x * H.z ∈ H.M := by
  constructor
  · intro hx
    rw [H.centralizer_eq] at hx
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (A := H.M) (B := zpowers H.z) (zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun l hl =>
        (H.comm_z hl))) hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    have hz2 : ∀ n : ℤ, H.z ^ n = 1 ∨ H.z ^ n = H.z := fun n => by
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · left
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← H.order_z]
      · right
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← H.order_z]
    rcases hz2 n with h | h
    · left; rw [h, mul_one]; exact hl
    · right; rw [h, mul_assoc, H.z_mul_self, mul_one]; exact hl
  · rintro (h | h)
    · exact H.centralizer_eq ▸ mem_sup_left h
    · have : x = (x * H.z) * H.z⁻¹ := by group
      rw [this, H.centralizer_eq]
      exact mul_mem (mem_sup_left h) (inv_mem (mem_sup_right (mem_zpowers _)))

theorem E_comm {a b : G} (ha : a ∈ H.E) (hb : b ∈ H.E) : a * b = b * a := by
  have h1 := H.sq_E _ (mul_mem ha hb)
  have h2 := H.sq_E a ha
  have h3 := H.sq_E b hb
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3] at this
  exact this

theorem z_comm_E {e : G} (he : e ∈ H.E) : e * H.z = H.z * e := H.comm_z (H.E_le_M he)

theorem z_not_mem_E : H.z ∉ H.E := fun h => H.z_not_mem_M (H.E_le_M h)

theorem le_L_of_isPGroup {P : Subgroup G} (hPM : P ≤ H.M) (hP : IsPGroup 2 P) : P ≤ H.L :=
  CFSG.OddStandard.L2Ree.le_of_isPGroup_of_odd_relIndex H.L_normal H.odd_relIndex hPM hP

theorem sylow_M : ∀ P : Subgroup G, P ≤ H.M → IsPGroup 2 P →
    ∃ g ∈ H.M, P ≤ H.E.map (MulAut.conj g).toMonoidHom :=
  CFSG.OddStandard.L2Ree.exists_conj_le_of_odd_relIndex H.L_le H.L_normal H.odd_relIndex H.sylow_E

end Setting

end CFSG.EvenSporadicStandard.ReeStd
