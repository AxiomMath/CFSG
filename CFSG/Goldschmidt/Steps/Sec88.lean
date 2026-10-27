module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec88a
import CFSG.Goldschmidt.Steps.Sec88e

public section

namespace CFSG.Goldschmidt

open CFSG.Open Sec8

theorem G88_of
    (h81 : S_G81) (h86 : S_G86) : S_G88 := by
  intro G _ _ S A hset h4 hS t htS ht2 htA
  obtain ⟨a₀, ha₀, hbad⟩ := exists_not_isGood h81 hset h4 htS ht2 htA
  have hx1 : t * a₀ ≠ 1 := fun h => htA (by
    rw [eq_inv_of_mul_eq_one_left h]
    exact A.inv_mem ha₀)
  obtain ⟨B, hB, hAB, hsup⟩ := direct_factor_of_not_isGood h81 h86 hset h4 hS
    ((S : Subgroup G).mul_mem htS (hset.le ha₀)) hx1 hbad
  have heq : (S : Subgroup G) ⊓ Subgroup.centralizer ({t * a₀} : Set G) =
      (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext s
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun hs => ?_
    have hsa : a₀ * s = s * a₀ :=
      Subgroup.mem_centralizer_iff.mp (le_centralizer hset h4 hs) a₀ ha₀
    constructor
    · intro h
      refine mul_right_cancel (b := a₀) ?_
      calc s * t * a₀ = s * (t * a₀) := by group
        _ = t * a₀ * s := h
        _ = t * (a₀ * s) := by group
        _ = t * (s * a₀) := by rw [hsa]
        _ = t * s * a₀ := by group
    · intro h
      calc s * (t * a₀) = s * t * a₀ := by group
        _ = t * s * a₀ := by rw [h]
        _ = t * (s * a₀) := by group
        _ = t * (a₀ * s) := by rw [hsa]
        _ = t * a₀ * s := by group
  rw [heq] at hB hsup
  exact ⟨B, hB, hAB, hsup⟩

end CFSG.Goldschmidt
