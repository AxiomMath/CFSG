module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14Ae5Model

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.AE5Mu

open CFSG.ClassicalInvolution.Q3.AE Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model

theorem sq_eq_one_of_perm_fixed_kList :
    ∀ a ∈ kList, ∀ i : Fin 4, a.perm i = i → a * a = 1 := by
  decide +kernel

theorem sq_eq_one_of_perm_fixed_kStarList :
    ∀ a ∈ kStarList, ∀ i : Fin 4, a.perm i = i → a * a = 1 := by
  decide +kernel

theorem sq_eq_one_of_perm_fixed {q p : Fin 5} {c : Bool} (hpq : p ≠ q) {a : Wr 5}
    (ha : a ∈ memAt (miss q) (card_miss q) c) (hp : a.perm p = p) : a * a = 1 := by
  have hpr : p ∈ Set.range (emb (miss q) (card_miss q)) := by
    rw [range_emb]
    simp [miss, hpq]
  obtain ⟨i, hi⟩ := hpr
  cases c
  · obtain ⟨a₀, ha₀, rfl⟩ := ha
    rw [embed_perm, ← hi, embedPerm_apply] at hp
    have h1 := (emb (miss q) (card_miss q)).injective hp
    have h2 := sq_eq_one_of_perm_fixed_kStarList a₀ ha₀ i h1
    rw [← map_mul, h2, map_one]
  · obtain ⟨a₀, ha₀, rfl⟩ := ha
    rw [embed_perm, ← hi, embedPerm_apply] at hp
    have h1 := (emb (miss q) (card_miss q)).injective hp
    have h2 := sq_eq_one_of_perm_fixed_kList a₀ ha₀ i h1
    rw [← map_mul, h2, map_one]

theorem eq_of_conj_zBar_eq {q p : Fin 5} {c : Bool} {x : AEQ 5}
    (hx : x ∈ memBar (miss q) (card_miss q) c) (hx2 : x * x ≠ 1)
    (hc : x * zBar (miss p) (card_miss p) * x⁻¹ = zBar (miss p) (card_miss p)) : p = q := by
  obtain ⟨a, ha, rfl⟩ := hx
  rw [zBar_conj_miss] at hc
  have h1 := miss_inj (eq_of_zBar_eq (by norm_num) hc)
  by_contra hpq
  exact hx2 (by rw [← map_mul, sq_eq_one_of_perm_fixed hpq ha h1, map_one])

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.AE5Mu
