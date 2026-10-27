module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Model

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y : G} {S₀ : Subgroup G} {n : G}

namespace Sect7Hyps

variable (hH : Sect7Hyps G L f s y S₀ n)
include hH

theorem comm_f {l : G} (hl : l ∈ L) : l * f = f * l := comm_f_of_mem hH.four hl

theorem comm_t {l : G} (hl : l ∈ L) : l * f ^ 2 = f ^ 2 * l :=
  (Commute.pow_right (hH.comm_f hl) 2).eq

theorem sq_mem_L : f ^ 2 ∈ L := hH.four.sq_mem

theorem f_pow_four : f ^ 4 = 1 := hH.four.pow_four

theorem conj_y_mem_f {a : G} (ha : a ∈ L ⊔ zpowers f) : y * a * y⁻¹ ∈ L ⊔ zpowers f := by
  obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup (fun l hl => hH.comm_f hl) ha
  have e : y * (l * f ^ i) * y⁻¹ = (y * l * y⁻¹) * (y * f * y⁻¹) ^ i := by
    rw [conj_zpow]; group
  rw [e, hH.yf]
  exact Subgroup.mul_mem_sup
    ((mem_normalizer_iff.1 (y_mem_normalizer hH.four hH.cent_eq) l).1 hl)
    (zpow_mem (inv_mem (mem_zpowers f)) i)

theorem normalizes_f {x : G} (hx : x * f ^ 2 = f ^ 2 * x) (z : G) :
    z ∈ L ⊔ zpowers f ↔ x * z * x⁻¹ ∈ L ⊔ zpowers f := by
  have hxN : x ∈ centralizer ({f ^ 2} : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hx.symm
  rw [hH.cent_eq] at hxN
  have hle : (L ⊔ zpowers f) ⊔ zpowers y ≤ normalizer ((L ⊔ zpowers f : Subgroup G) : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    refine zpowers_le.2 ?_
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hH.conj_y_mem_f hz
    · intro hz
      have h1 := hH.conj_y_mem_f hz
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hH.yy
      have e : y * (y * z * y⁻¹) * y⁻¹ = z := by
        rw [hyinv]
        calc y * (y * z * y) * y = (y * y) * z * (y * y) := by group
          _ = z := by rw [hH.yy]; group
      rw [e] at h1
      exact h1
  exact mem_normalizer_iff.1 (hle hxN) z

theorem conj_f_mem_y {z : G} (hz : z ∈ L ⊔ zpowers y) : f * z * f⁻¹ ∈ L ⊔ zpowers y := by
  rcases H1_cases hH.four hH.yy hH.cent_eq hz with h | ⟨a, ha, rfl⟩
  · have : f * z * f⁻¹ = z := by
      have := hH.comm_f h
      calc f * z * f⁻¹ = z * f * f⁻¹ := by rw [← this]
        _ = z := by group
    rw [this]
    exact Subgroup.mem_sup_left h
  · have hfa : f * a = a * f := (hH.comm_f ha).symm
    have hyf : y * f * y⁻¹ = f⁻¹ := hH.yf
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hH.yy
    have hfy : f * y * f⁻¹ = f ^ 2 * y := by
      have h1 : y * f⁻¹ * y = f := by
        have h1' : y * f⁻¹ * y⁻¹ = f := by
          calc y * f⁻¹ * y⁻¹ = (y * f * y⁻¹)⁻¹ := by group
            _ = f := by rw [hyf]; group
        rw [hyinv] at h1'
        exact h1'
      calc f * y * f⁻¹ = f * (y * f⁻¹ * y) * y := by
            have : y * y = 1 := hH.yy
            calc f * y * f⁻¹ = f * y * f⁻¹ * (y * y) := by rw [this]; group
              _ = f * (y * f⁻¹ * y) * y := by group
        _ = f * f * y := by rw [h1]
        _ = f ^ 2 * y := by rw [sq]
    have e : f * (a * y) * f⁻¹ = (a * f ^ 2) * y := by
      calc f * (a * y) * f⁻¹ = (f * a) * (y * f⁻¹) := by group
        _ = a * (f * y * f⁻¹) := by rw [hfa]; group
        _ = a * (f ^ 2 * y) := by rw [hfy]
        _ = (a * f ^ 2) * y := by group
    rw [e]
    exact Subgroup.mul_mem_sup (L.mul_mem ha hH.sq_mem_L) (mem_zpowers y)

theorem conj_finv_mem_y {z : G} (hz : z ∈ L ⊔ zpowers y) : f⁻¹ * z * f ∈ L ⊔ zpowers y := by
  rcases H1_cases hH.four hH.yy hH.cent_eq hz with h | ⟨a, ha, rfl⟩
  · have : f⁻¹ * z * f = z := by
      have := hH.comm_f h
      calc f⁻¹ * z * f = f⁻¹ * (z * f) := by group
        _ = f⁻¹ * (f * z) := by rw [this]
        _ = z := by group
    rw [this]
    exact Subgroup.mem_sup_left h
  · have hfa : f⁻¹ * a = a * f⁻¹ := by
      have := hH.comm_f ha
      calc f⁻¹ * a = f⁻¹ * a * f * f⁻¹ := by group
        _ = f⁻¹ * (a * f) * f⁻¹ := by group
        _ = f⁻¹ * (f * a) * f⁻¹ := by rw [this]
        _ = a * f⁻¹ := by group
    have hyf : y * f * y⁻¹ = f⁻¹ := hH.yf
    have hfy : f⁻¹ * y * f = f⁻¹ ^ 2 * y := by
      have h1 : y * f = f⁻¹ * y := by
        calc y * f = (y * f * y⁻¹) * y := by group
          _ = f⁻¹ * y := by rw [hyf]
      calc f⁻¹ * y * f = f⁻¹ * (y * f) := by group
        _ = f⁻¹ * (f⁻¹ * y) := by rw [h1]
        _ = f⁻¹ ^ 2 * y := by group
    have hsq : f⁻¹ ^ 2 ∈ L := by
      have : f⁻¹ ^ 2 = (f ^ 2)⁻¹ := by group
      rw [this]
      exact L.inv_mem hH.sq_mem_L
    have e : f⁻¹ * (a * y) * f = (a * f⁻¹ ^ 2) * y := by
      calc f⁻¹ * (a * y) * f = (f⁻¹ * a) * (y * f) := by group
        _ = a * (f⁻¹ * (y * f)) := by rw [hfa]; group
        _ = a * (f⁻¹ * y * f) := by group
        _ = a * (f⁻¹ ^ 2 * y) := by rw [hfy]
        _ = (a * f⁻¹ ^ 2) * y := by group
    rw [e]
    exact Subgroup.mul_mem_sup (L.mul_mem ha hsq) (mem_zpowers y)

theorem normalizes_y {x : G} (hx : x * f ^ 2 = f ^ 2 * x) (z : G) :
    z ∈ L ⊔ zpowers y ↔ x * z * x⁻¹ ∈ L ⊔ zpowers y := by
  have hxN : x ∈ centralizer ({f ^ 2} : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hx.symm
  rw [hH.cent_eq] at hxN
  have hle : (L ⊔ zpowers f) ⊔ zpowers y ≤ normalizer ((L ⊔ zpowers y : Subgroup G) : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_trans le_sup_left Subgroup.le_normalizer
    · refine zpowers_le.2 ?_
      rw [mem_normalizer_iff]
      intro z
      constructor
      · exact hH.conj_f_mem_y
      · intro hz
        have h1 := hH.conj_finv_mem_y hz
        have e : f⁻¹ * (f * z * f⁻¹) * f = z := by group
        rw [e] at h1
        exact h1
    · exact zpowers_le.2 (le_trans le_sup_right Subgroup.le_normalizer (mem_zpowers y))
  exact mem_normalizer_iff.1 (hle hxN) z

end Sect7Hyps

end CFSG.EvenSporadicStandard.TwoHS
