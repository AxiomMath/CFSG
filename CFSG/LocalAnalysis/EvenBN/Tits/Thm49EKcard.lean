module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup

private theorem conj_mul_of_commute {G : Type*} [Group G] {x c : G} (h : G)
    (hc : c * x = x * c) : h * c * x * (h * c)⁻¹ = h * x * h⁻¹ := by
  rw [mul_inv_rev, mul_assoc h c x, hc]
  simp [mul_assoc]

theorem card_mul_card_inf_centralizer_le {G : Type*} [Group G] [Finite G] (H : Subgroup G) (x : G)
    (S : Finset G) (hS : ∀ s ∈ S, ∃ h ∈ H, h * x * h⁻¹ = s) :
    S.card * Nat.card ↥(H ⊓ centralizer ({x} : Set G)) ≤ Nat.card ↥H := by
  choose! g hgH hgx using hS
  have hmem : ∀ (s : S) (c : ↥(H ⊓ centralizer ({x} : Set G))), g s * (c : G) ∈ H :=
    fun s c => H.mul_mem (hgH s s.2) (mem_inf.mp c.2).1
  have hcomm : ∀ c : ↥(H ⊓ centralizer ({x} : Set G)), (c : G) * x = x * c := fun c =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2
  have hinj : Function.Injective
      (fun p : S × ↥(H ⊓ centralizer ({x} : Set G)) => (⟨g p.1 * p.2, hmem p.1 p.2⟩ : ↥H)) := by
    rintro ⟨s, c⟩ ⟨s', c'⟩ hp
    have hp' : g s * (c : G) = g s' * (c' : G) := congrArg Subtype.val hp
    have hss : (s : G) = s' := by
      rw [← hgx s s.2, ← hgx s' s'.2, ← conj_mul_of_commute (g s) (hcomm c),
        ← conj_mul_of_commute (g s') (hcomm c'), hp']
    have hss' : s = s' := Subtype.ext hss
    subst hss'
    have hcc : c = c' := Subtype.ext (mul_left_cancel hp')
    rw [hcc]
  have hle := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_eq_finsetCard] at hle

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
