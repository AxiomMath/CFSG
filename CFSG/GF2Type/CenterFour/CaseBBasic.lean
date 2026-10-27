module

public import CFSG.GF2Type.CenterFour.SettingConj
public import CFSG.GF2Type.CenterFour.Basic

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

theorem CaseB.not_mem_core (hC : Config z n) {z₁ : G}
    (hK : z₁ ∉ centralizer (centerAt z : Set G)) : z₁ ∉ coreAt z :=
  fun h => hK (hC.core_le_centralizer_center h)

theorem CaseB.not_mem_centralizer_center (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) :
    z ∉ centralizer (centerAt (g⁻¹ * z * g) : Set G) := by
  intro h
  have hle : centerAt (g⁻¹ * z * g) ≤ centralizer ({z} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h y hy)
  rw [centerAt_conj z g] at hle
  exact CaseB.not_mem_core hC hK ((hC.center_le_iff g).mp hle)

theorem CaseB.mem (hC : Config z n) {z₁ : G} (hH : z₁ ∈ centralizer ({z} : Set G)) :
    z ∈ coreAt z ⊓ centralizer ({z₁} : Set G) :=
  ⟨hC.mem_core,
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hH).symm⟩

private theorem isMulCommutative_of_sq_eq_one (U : Subgroup G) (h : ∀ x ∈ U, x ^ 2 = 1) :
    IsMulCommutative U := by
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  change (a : G) * (b : G) = (b : G) * (a : G)
  have inv_eq : ∀ x ∈ U, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h x hx)
  have hab : ((a : G) * (b : G)) ^ 2 = 1 := h _ (U.mul_mem a.2 b.2)
  have hsq : (a : G) * (b : G) = ((a : G) * (b : G))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← sq]; exact hab)
  rw [mul_inv_rev, inv_eq _ a.2, inv_eq _ b.2] at hsq
  exact hsq

private theorem sq_mem_centralizer_centerAt_conj (hC : Config z n) {g c : G}
    (hc : c ∈ centralizer ({g⁻¹ * z * g} : Set G)) :
    c ^ 2 ∈ centralizer (centerAt (g⁻¹ * z * g) : Set G) := by
  have hC₁ : Config (g⁻¹ * z * g) n := hC.conj g
  by_cases hcZ : c ∈ centralizer (centerAt (g⁻¹ * z * g) : Set G)
  · exact pow_mem hcZ 2
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : c * y * c⁻¹ = y⁻¹ := hC₁.inv_of_not_mem_centralizer hc hcZ hy
  have h2 : c * y⁻¹ * c⁻¹ = y := by
    have h := hC₁.inv_of_not_mem_centralizer hc hcZ (inv_mem hy)
    rwa [inv_inv] at h
  have e1 : c * y = y⁻¹ * c := by
    calc c * y = (c * y * c⁻¹) * c := by group
      _ = y⁻¹ * c := by rw [h1]
  have e2 : c * y⁻¹ = y * c := by
    calc c * y⁻¹ = (c * y⁻¹ * c⁻¹) * c := by group
      _ = y * c := by rw [h2]
  calc y * c ^ 2 = (y * c) * c := by rw [sq, mul_assoc]
    _ = (c * y⁻¹) * c := by rw [e2]
    _ = c * (y⁻¹ * c) := by group
    _ = c * (c * y) := by rw [e1]
    _ = c ^ 2 * y := by rw [sq, mul_assoc]

theorem CaseB.isElemAbelian (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) :
    CFSG.Open.IsElemAbelian 2 (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) := by
  have hsq : ∀ c ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G), c ^ 2 = 1 := by
    intro c hc
    rcases hC.sq_eq c (Subgroup.mem_inf.mp hc).1 with h | h
    · exact h
    · exfalso
      have hmem := sq_mem_centralizer_centerAt_conj hC (Subgroup.mem_inf.mp hc).2
      rw [h] at hmem
      exact CaseB.not_mem_centralizer_center hC hH hK hmem
  exact ⟨isMulCommutative_of_sq_eq_one _ hsq, hsq⟩

end CFSG.GF2Type.CenterFour
