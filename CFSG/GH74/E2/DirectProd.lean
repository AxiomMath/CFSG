module

public import CFSG.GH74.E2.Cl2Rank

public section

namespace CFSG.GH74.E2

open Subgroup

variable {G : Type*} [Group G]

theorem mul_mem_sup_of_commute {A B : Subgroup G} {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    a * b ∈ A ⊔ B := Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

@[expose] def prodSupHom (A B : Subgroup G) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    (↥A × ↥B) →* ↥(A ⊔ B) where
  toFun p := ⟨(p.1 : G) * p.2, mul_mem_sup_of_commute p.1.2 p.2.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by
    change ((p.1 : G) * q.1) * (p.2 * q.2) = ((p.1 : G) * p.2) * (q.1 * q.2)
    calc ((p.1 : G) * q.1) * (p.2 * q.2) = (p.1 : G) * (q.1 * p.2) * q.2 := by
          simp only [mul_assoc]
      _ = (p.1 : G) * (p.2 * q.1) * q.2 := by rw [hcomm q.1 q.1.2 p.2 p.2.2]
      _ = ((p.1 : G) * p.2) * (q.1 * q.2) := by simp only [mul_assoc])

theorem prodSupHom_apply (A B : Subgroup G) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (p : ↥A × ↥B) : ((prodSupHom A B hcomm p : ↥(A ⊔ B)) : G) = p.1 * p.2 := rfl

theorem prodSupHom_bijective (A B : Subgroup G) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : A ⊓ B = ⊥) : Function.Bijective (prodSupHom A B hcomm) := by
  refine ⟨?_, ?_⟩
  · intro p q h
    have h1 : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val h
    have h2 : ((q.1 : G)⁻¹ * p.1) = q.2 * (p.2 : G)⁻¹ := by
      have e1 : (q.1 : G)⁻¹ * (p.1 * p.2) = q.2 := by rw [h1, inv_mul_cancel_left]
      calc (q.1 : G)⁻¹ * p.1 = ((q.1 : G)⁻¹ * (p.1 * p.2)) * (p.2 : G)⁻¹ := by group
        _ = q.2 * (p.2 : G)⁻¹ := by rw [e1]
    have hA : (q.1 : G)⁻¹ * p.1 ∈ A := Subgroup.mul_mem _ (Subgroup.inv_mem _ q.1.2) p.1.2
    have hB : (q.1 : G)⁻¹ * p.1 ∈ B := by
      rw [h2]; exact Subgroup.mul_mem _ q.2.2 (Subgroup.inv_mem _ p.2.2)
    have hbot : (q.1 : G)⁻¹ * p.1 = 1 := by
      have : (q.1 : G)⁻¹ * p.1 ∈ A ⊓ B := ⟨hA, hB⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact this
    have hp1 : (p.1 : G) = q.1 := by
      have := congrArg (fun x => (q.1 : G) * x) hbot
      simpa using this
    have hp2 : (p.2 : G) = q.2 := by
      have h3 : (p.1 : G) * p.2 = p.1 * q.2 := by rw [h1, ← hp1]
      exact mul_left_cancel h3
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_commute hcomm).1 hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

@[expose] noncomputable def prodSupEquiv (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : A ⊓ B = ⊥) : (↥A × ↥B) ≃* ↥(A ⊔ B) :=
  MulEquiv.ofBijective (prodSupHom A B hcomm) (prodSupHom_bijective A B hcomm hdisj)

theorem prodSupEquiv_apply (A B : Subgroup G) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : A ⊓ B = ⊥) (p : ↥A × ↥B) :
    ((prodSupEquiv A B hcomm hdisj p : ↥(A ⊔ B)) : G) = p.1 * p.2 := rfl

end CFSG.GH74.E2
