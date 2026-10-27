module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyDef

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

theorem chi_conj {H : Type*} [Group H] (χ : H →* ℤˣ) (a u : H) : χ (a * u * a⁻¹) = χ u := by
  rw [map_mul, map_mul, map_inv, mul_comm (χ a) (χ u), mul_assoc, mul_inv_cancel, mul_one]

theorem chi_val {G : Type} [Group G] {r : G} {Θ : HModel →* G}
    (χ : ↥(centralizer ({r} : Set G)) →* ℤˣ) (b : ℤˣ)
    (hχ : ∀ (d : DihedralGroup 4) (c : Z3) (σ : Equiv.Perm (Fin 5))
      (h : Θ (d, c, σ) ∈ centralizer ({r} : Set G)),
      χ ⟨Θ (d, c, σ), h⟩ = dihChar b d * Equiv.Perm.sign σ)
    {x : G} (hx : x ∈ centralizer ({r} : Set G)) {d : DihedralGroup 4} {c : Z3}
    {σ : Equiv.Perm (Fin 5)} (hxe : Θ (d, c, σ) = x) :
    χ ⟨x, hx⟩ = dihChar b d * Equiv.Perm.sign σ := by
  subst hxe
  exact hχ d c σ hx

theorem mem_cent_of_comm {G : Type} [Group G] {r x : G} (h : x * r = r * x) :
    x ∈ centralizer ({r} : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  rw [ha]
  exact h.symm

theorem exists_sr_of_not_mem {G : Type} [Group G] {L : Subgroup G} {f y : G}
    {Θ : HModel →* G} (hc : FyCoset L f y Θ) {d : DihedralGroup 4} {c : Z3}
    {σ : Equiv.Perm (Fin 5)} (h : Θ (d, c, σ) ∉ L ⊔ zpowers f) : ∃ k : ZMod 4,
    d = DihedralGroup.sr k := by
  cases d with
  | r k => exact absurd ((hc.mem_f _ c σ).2 ⟨k, rfl⟩) h
  | sr k => exact ⟨k, rfl⟩

end CFSG.EvenSporadicStandard.TwoHS
