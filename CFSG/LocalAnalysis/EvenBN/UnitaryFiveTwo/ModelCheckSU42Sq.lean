module

public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Swap

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] {t : G} {K₀ : Subgroup G}

theorem conj_mem_map {x : G} (hx : x ∈ K₀) : t * x * t⁻¹ ∈ K₀.map (MulAut.conj t).toMonoidHom :=
  ⟨x, hx, rfl⟩

theorem comm_of_commutator_eq_bot (hK : ⁅K₀, K₀.map (MulAut.conj t).toMonoidHom⁆ = ⊥) {x y : G}
    (hx : x ∈ K₀) (hy : y ∈ K₀) : x * (t * y * t⁻¹) = t * y * t⁻¹ * x := by
  have h : ⁅x, t * y * t⁻¹⁆ ∈ ⁅K₀, K₀.map (MulAut.conj t).toMonoidHom⁆ :=
    commutator_mem_commutator hx (conj_mem_map hy)
  rwa [hK, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h

variable (hK : ⁅K₀, K₀.map (MulAut.conj t).toMonoidHom⁆ = ⊥)

variable (t K₀) in
@[expose] def swapHom : K₀ →* G where
  toFun x := (x : G) * (t * x * t⁻¹)
  map_one' := by simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul]
    have h := comm_of_commutator_eq_bot hK y.2 x.2
    calc (x : G) * y * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
      _ = x * (t * x * t⁻¹ * y) * (t * y * t⁻¹) := by rw [h]
      _ = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹)) := by group

theorem swapHom_apply (x : K₀) : swapHom t K₀ hK x = x * (t * x * t⁻¹) :=
  rfl

theorem swapHom_comm (ht : t * t = 1) (x : K₀) : t * swapHom t K₀ hK x = swapHom t K₀ hK x * t := by
  have h := comm_of_commutator_eq_bot hK x.2 x.2
  have e : t * ((x : G) * (t * x * t⁻¹)) * t⁻¹ = x * (t * x * t⁻¹) := by
    calc t * ((x : G) * (t * x * t⁻¹)) * t⁻¹ = t * x * t⁻¹ * ((t * t) * x * (t * t)⁻¹) := by group
      _ = t * x * t⁻¹ * x := by rw [ht, one_mul, inv_one, mul_one]
      _ = x * (t * x * t⁻¹) := h.symm
  rw [swapHom_apply]
  calc t * ((x : G) * (t * x * t⁻¹)) = t * ((x : G) * (t * x * t⁻¹)) * t⁻¹ * t := by group
    _ = x * (t * x * t⁻¹) * t := by rw [e]

theorem mem_inf_of_swapHom_eq_one {x : K₀} (h : swapHom t K₀ hK x = 1) :
    (x : G) ∈ K₀ ⊓ K₀.map (MulAut.conj t).toMonoidHom := by
  rw [swapHom_apply, mul_eq_one_iff_inv_eq] at h
  refine mem_inf.2 ⟨x.2, ⟨(x : G)⁻¹, inv_mem x.2, ?_⟩⟩
  change t * (x : G)⁻¹ * t⁻¹ = x
  rw [show t * (x : G)⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group, ← h, inv_inv]

theorem swapHom_injective (hI : K₀ ⊓ K₀.map (MulAut.conj t).toMonoidHom = ⊥) :
    Function.Injective (swapHom t K₀ hK) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h := mem_inf_of_swapHom_eq_one hK hx
  rw [hI, mem_bot] at h
  exact Subtype.ext h

theorem exists_eq_swapHom_mul (ht : t * t = 1) {g : G}
    (hg : g ∈ K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom) (hgt : t * g = g * t) :
    ∃ b : K₀, ∃ z ∈ K₀ ⊓ K₀.map (MulAut.conj t).toMonoidHom,
      t * z = z * t ∧ g = swapHom t K₀ hK b * z := by
  obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha c hc => by
      obtain ⟨y, hy, rfl⟩ := hc
      exact comm_of_commutator_eq_bot hK ha hy) hg
  change t * (a * (t * b * t⁻¹)) = a * (t * b * t⁻¹) * t at hgt
  have e₁ : t * (a * (t * b * t⁻¹)) * t⁻¹ = a * (t * b * t⁻¹) := by rw [hgt, mul_inv_cancel_right]
  have e₂ : t * (a * (t * b * t⁻¹)) * t⁻¹ = t * a * t⁻¹ * ((t * t) * b * (t * t)⁻¹) := by group
  rw [ht, one_mul, inv_one, mul_one] at e₂
  have hab : a * (t * b * t⁻¹) = b * (t * a * t⁻¹) := by
    rw [← e₁, e₂, comm_of_commutator_eq_bot hK hb ha]
  have hzt : t * (a * b⁻¹) * t⁻¹ = b⁻¹ * a := by
    calc t * (a * b⁻¹) * t⁻¹ = b⁻¹ * (b * (t * a * t⁻¹)) * (t * b * t⁻¹)⁻¹ := by group
      _ = b⁻¹ * (a * (t * b * t⁻¹)) * (t * b * t⁻¹)⁻¹ := by rw [hab]
      _ = b⁻¹ * a := by group
  have hzK : b⁻¹ * a ∈ K₀ := mul_mem (inv_mem hb) ha
  have hg' : a * (t * b * t⁻¹) = swapHom t K₀ hK ⟨b, hb⟩ * (b⁻¹ * a) := by
    rw [swapHom_apply]
    have hc := comm_of_commutator_eq_bot hK hzK hb
    calc a * (t * b * t⁻¹) = b * (b⁻¹ * a * (t * b * t⁻¹)) := by group
      _ = b * (t * b * t⁻¹ * (b⁻¹ * a)) := by rw [hc]
      _ = b * (t * b * t⁻¹) * (b⁻¹ * a) := by group
  refine ⟨⟨b, hb⟩, b⁻¹ * a, mem_inf.2 ⟨hzK, ⟨a * b⁻¹, mul_mem ha (inv_mem hb), hzt⟩⟩, ?_, hg'⟩
  have h₁ : Commute t (swapHom t K₀ hK ⟨b, hb⟩)⁻¹ :=
    (show Commute t _ from swapHom_comm hK ht ⟨b, hb⟩).inv_right
  have h₂ : Commute t (a * (t * b * t⁻¹)) := hgt
  have hz : b⁻¹ * a = (swapHom t K₀ hK ⟨b, hb⟩)⁻¹ * (a * (t * b * t⁻¹)) := by
    rw [hg', inv_mul_cancel_left]
  rw [hz]
  exact (h₁.mul_right h₂).eq

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Swap
