module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Defs
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup CFSG.Quasithin

variable {G : Type*} [Group G] {t : G} {L : Subgroup G}

namespace ShapeA

theorem commute_of_mem (hA : ShapeA t L) {l : G} (hl : l ∈ L) : l * t = t * l :=
  mem_centralizer_singleton_iff.1 (hA.le_centralizer hl)

theorem mul_self (hA : ShapeA t L) : t * t = 1 := by
  rw [← pow_two, ← hA.orderOf_eq, pow_orderOf_eq_one]

theorem mem_zpowers_iff (hA : ShapeA t L) {z : G} : z ∈ zpowers t ↔ z = 1 ∨ z = t := by
  constructor
  · rintro ⟨k, rfl⟩
    change t ^ k = 1 ∨ t ^ k = t
    rw [← zpow_mod_orderOf, hA.orderOf_eq]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h]
    · exact Or.inl (zpow_zero t)
    · exact Or.inr (zpow_one t)
  · rintro (h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers t

theorem mem_iff (hA : ShapeA t L) {x : G} :
    x ∈ centralizer ({t} : Set G) ↔ ∃ l ∈ L, x = l ∨ x = l * t := by
  constructor
  · intro hx
    rw [hA.centralizer_eq] at hx
    obtain ⟨l, hl, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => by
        rcases hA.mem_zpowers_iff.1 hb with rfl | rfl
        · rw [mul_one, one_mul]
        · exact hA.commute_of_mem ha) hx
    rcases hA.mem_zpowers_iff.1 hz with rfl | rfl
    · exact ⟨l, hl, Or.inl (mul_one l)⟩
    · exact ⟨l, hl, Or.inr rfl⟩
  · rintro ⟨l, hl, rfl | rfl⟩
    · exact hA.le_centralizer hl
    · exact mul_mem (hA.le_centralizer hl) (mem_centralizer_singleton_iff.2 rfl)

theorem mem_of_odd_orderOf (hA : ShapeA t L) {x : G} (hx : x ∈ centralizer ({t} : Set G))
    (hodd : Odd (orderOf x)) : x ∈ L := by
  obtain ⟨l, hl, rfl | rfl⟩ := hA.mem_iff.1 hx
  · exact hl
  · exfalso
    obtain ⟨m, hm⟩ := hodd
    have h1 : (l * t) ^ orderOf (l * t) = 1 := pow_orderOf_eq_one _
    have hc : Commute l t := hA.commute_of_mem hl
    rw [hc.mul_pow, hm, pow_succ t, pow_mul t, pow_two, hA.mul_self, one_pow, one_mul] at h1
    apply hA.not_mem
    have h2 : t = (l ^ (2 * m + 1))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_mem (pow_mem hl _)

theorem not_mem_closure_odd (hA : ShapeA t L) :
    t ∉ closure {g : G | g * t = t * g ∧ Odd (orderOf g)} := by
  intro ht
  refine hA.not_mem ((closure_le L).2 (fun g hg => ?_) ht)
  exact hA.mem_of_odd_orderOf (mem_centralizer_singleton_iff.2 hg.1) hg.2

end ShapeA

theorem eq_sup_of_le (hA : ShapeA t L) {U : Subgroup G} (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U)
    {V : Subgroup G} (hVH : V ≤ centralizer ({t} : Set G)) (hV : IsPGroup 2 V)
    (hUV : U ⊔ zpowers t ≤ V) : V = U ⊔ zpowers t := by
  refine le_antisymm (fun x hx => ?_) hUV
  have h1 : V ⊓ L = U :=
    hUmax _ inf_le_right (hV.to_le inf_le_left) (le_inf (le_sup_left.trans hUV) hUL)
  have htV : t ∈ V := hUV (mem_sup_right (mem_zpowers t))
  obtain ⟨l, hl, rfl | rfl⟩ := hA.mem_iff.1 (hVH hx)
  · exact mem_sup_left (by rw [← h1]; exact ⟨hx, hl⟩)
  · have hlV : l ∈ V := by simpa using V.mul_mem hx (V.inv_mem htV)
    exact mul_mem (mem_sup_left (by rw [← h1]; exact ⟨hlV, hl⟩))
      (mem_sup_right (mem_zpowers t))

end CFSG.EvenSmallLie.OmegaEight.Stage1
