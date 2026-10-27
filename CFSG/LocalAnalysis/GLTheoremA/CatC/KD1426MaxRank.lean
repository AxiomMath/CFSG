module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426E27
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Common
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs

public section

open CFSG.Open

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426MaxRank

variable {Y : Type} [Group Y]

theorem isElemAbelian_sup_of_commute {H H' : Subgroup Y} (hH : IsElemAbelian 3 H)
    (hH' : IsElemAbelian 3 H') (hc : ∀ h ∈ H, ∀ h' ∈ H', h * h' = h' * h) :
    IsElemAbelian 3 (H ⊔ H') := by
  rw [Subgroup.sup_eq_closure]
  apply KD1426E27.isElemAbelian_closure
  · intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have := hH.1.is_comm.comm (⟨x, hx⟩ : ↥H) ⟨y, hy⟩
      exact congrArg Subtype.val this
    · exact hc x hx y hy
    · exact (hc y hy x hx).symm
    · have := hH'.1.is_comm.comm (⟨x, hx⟩ : ↥H') ⟨y, hy⟩
      exact congrArg Subtype.val this
  · intro x hx
    rcases hx with hx | hx
    · exact hH.2 x hx
    · exact hH'.2 x hx

theorem max_rank_bound [Finite Y] {B : Subgroup Y} (hBel : IsElemAbelian 3 B)
    (hmax : IsMaxRankIn 3 B ⊤) {H B0 : Subgroup Y} (hH : IsElemAbelian 3 H) (hB0 : B0 ≤ B)
    (hc : ∀ h ∈ H, ∀ b ∈ B0, h * b = b * h) (hdisj : H ⊓ B0 = ⊥) :
    Nat.card H * Nat.card B0 ≤ Nat.card B := by
  have hB0el : IsElemAbelian 3 B0 := KD1426Common.isElemAbelian_of_le hB0 hBel
  have hnorm : B0 ≤ Subgroup.normalizer (H : Set Y) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : h * b = b * h := hc h hh b hb
      have e : b * h * b⁻¹ = h := by
        calc b * h * b⁻¹ = (b * h) * b⁻¹ := rfl
          _ = (h * b) * b⁻¹ := by rw [h1]
          _ = h := by group
      rw [e]
      exact hh
    · intro hg
      have hgb : (b * h * b⁻¹) * b = b * (b * h * b⁻¹) := hc _ hg b hb
      have hinv : b⁻¹ * (b * h * b⁻¹) * b = b * h * b⁻¹ := by
        calc b⁻¹ * (b * h * b⁻¹) * b = b⁻¹ * ((b * h * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * h * b⁻¹)) := by rw [hgb]
          _ = b * h * b⁻¹ := by group
      have e2 : h = b⁻¹ * (b * h * b⁻¹) * b := by group
      rw [e2, hinv]
      exact hg
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hdisj, Subgroup.card_bot, mul_one] at hcard
  have hle := hmax (H ⊔ B0) le_top (isElemAbelian_sup_of_commute hH hB0el hc)
  rw [hcard] at hle
  exact hle

end CFSG.LocalAnalysis.GLTheoremA.KD1426MaxRank

end
