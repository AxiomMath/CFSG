module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveSym8

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv

variable {G : Type*} [Group G]

structure FiveTriple (L : Subgroup G) (v r u₁ u₂ : G) : Prop where
  r_mem : r ∈ L
  u₁_mem : u₁ ∈ L
  u₂_mem : u₂ ∈ L
  r_comm : r * v = v * r
  u₁_comm : u₁ * v = v * u₁
  u₂_comm : u₂ * v = v * u₂
  r_ord : orderOf r = 5
  u₁_sq : u₁ * u₁ = 1
  u₂_sq : u₂ * u₂ = 1
  u_cube : (u₁ * u₂) ^ 3 = 1
  u_ne : u₁ * u₂ ≠ 1
  u₁_r : u₁ * r = r * u₁
  u₂_r : u₂ * r = r * u₂

theorem exists_fiveTriple {L : Subgroup G} {v : G}
    (e : ↥(centralizer ({v} : Set G) ⊓ L) ≃* Perm (Fin 8)) :
    ∃ r u₁ u₂ : G, FiveTriple L v r u₁ u₂ := by
  set T : Subgroup G := centralizer ({v} : Set G) ⊓ L with hT
  have hmemv : ∀ a : Perm (Fin 8), ((e.symm a : ↥T) : G) * v = v * ((e.symm a : ↥T) : G) :=
    fun a => mem_centralizer_singleton_iff.1 (e.symm a).2.1
  have hmemL : ∀ a : Perm (Fin 8), ((e.symm a : ↥T) : G) ∈ L := fun a => (e.symm a).2.2
  have hmulv : ∀ a b : Perm (Fin 8), ((e.symm a : ↥T) : G) * ((e.symm b : ↥T) : G) =
      ((e.symm (a * b) : ↥T) : G) := fun a b => by rw [map_mul]; rfl
  have hpow : ∀ (a : Perm (Fin 8)) (k : ℕ), ((e.symm a : ↥T) : G) ^ k =
      ((e.symm (a ^ k) : ↥T) : G) := fun a k => by rw [map_pow]; rfl
  have hone : ∀ a : Perm (Fin 8), ((e.symm a : ↥T) : G) = 1 → a = 1 := by
    intro a ha
    have : e.symm a = 1 := Subtype.ext ha
    exact e.symm.injective (by rw [this, map_one])
  have hone' : ((e.symm (1 : Perm (Fin 8)) : ↥T) : G) = 1 := by rw [map_one]; rfl
  refine ⟨(e.symm sym8C : G), (e.symm sym8U1 : G), (e.symm sym8U2 : G),
    ⟨hmemL _, hmemL _, hmemL _, hmemv _, hmemv _, hmemv _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_sym8C
  · rw [hmulv, sym8U1_mul_self, hone']
  · rw [hmulv, sym8U2_mul_self, hone']
  · rw [hmulv, hpow, sym8_cube, hone']
  · intro h
    rw [hmulv] at h
    exact sym8_U1U2_ne_one (hone _ h)
  · rw [hmulv, hmulv, sym8U1_comm_C]
  · rw [hmulv, hmulv, sym8U2_comm_C]

theorem FiveTriple.mul_t {L : Subgroup G} {t v r u₁ u₂ : G} (h : FiveTriple L v r u₁ u₂)
    (ht : t ∈ centralizer (L : Set G)) : FiveTriple L (t * v) r u₁ u₂ := by
  have hc : ∀ x ∈ L, x * (t * v) = (t * v) * x ↔ x * v = v * x := by
    intro x hx
    have htx : x * t = t * x := mem_centralizer_iff.1 ht x hx
    constructor
    · intro hh
      have h1 : t * (x * v) = t * (v * x) := by
        calc t * (x * v) = (x * t) * v := by rw [htx, mul_assoc]
          _ = x * (t * v) := by rw [mul_assoc]
          _ = (t * v) * x := hh
          _ = t * (v * x) := by rw [mul_assoc]
      exact mul_left_cancel h1
    · intro hh
      calc x * (t * v) = (x * t) * v := by rw [mul_assoc]
        _ = t * (x * v) := by rw [htx, mul_assoc]
        _ = t * (v * x) := by rw [hh]
        _ = (t * v) * x := by rw [mul_assoc]
  exact ⟨h.r_mem, h.u₁_mem, h.u₂_mem, (hc r h.r_mem).2 h.r_comm, (hc u₁ h.u₁_mem).2 h.u₁_comm,
    (hc u₂ h.u₂_mem).2 h.u₂_comm, h.r_ord, h.u₁_sq, h.u₂_sq, h.u_cube, h.u_ne, h.u₁_r, h.u₂_r⟩

end CFSG.EvenSporadicStandard.HSStd
