module

public import CFSG.Dihedral.ASevenCyclingWords
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

theorem a7U_fixedBy_zero_eq_bot :
    a7U ⊓ Subgroup.centralizer (a7LocalFourgroup 0 : Set ASevenCertificateGroup) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 1
  have hu := hx.1
  change x = 1 ∨ x = a7a ∨ x = a7a ^ 2 at hu
  have hs : a7s ∈ a7LocalFourgroup 0 := by
    change a7s ∈ ({a7t * (a7s * a7v ^ (0 : Fin 2).val), a7t,
      a7s * a7v ^ (0 : Fin 2).val, 1} : Set ASevenCertificateGroup)
    simp
  rcases hu with h | rfl | rfl
  · exact h
  · exact False.elim ((by decide : a7s * a7a ≠ a7a * a7s)
      (Subgroup.mem_centralizer_iff.mp hx.2 a7s hs))
  · exact False.elim ((by decide : a7s * a7a ^ 2 ≠ a7a ^ 2 * a7s)
      (Subgroup.mem_centralizer_iff.mp hx.2 a7s hs))

theorem a7U_le_of_inf_ne_bot (H : Subgroup ASevenCertificateGroup)
    (h : a7U ⊓ H ≠ ⊥) : a7U ≤ H := by
  have haH : a7a ∈ H := by
    by_contra ha
    apply h
    apply le_antisymm _ bot_le
    intro x hx
    change x = 1
    have hu := hx.1
    change x = 1 ∨ x = a7a ∨ x = a7a ^ 2 at hu
    rcases hu with h1 | rfl | rfl
    · exact h1
    · exact (ha hx.2).elim
    · have hsquare : (a7a ^ 2) ^ 2 ∈ H := H.pow_mem hx.2 2
      have heq : (a7a ^ 2) ^ 2 = a7a := by decide
      rw [heq] at hsquare
      exact (ha hsquare).elim
  rw [a7U_eq_zpowers]
  exact Subgroup.zpowers_le.mpr haH

theorem a7U_inf_eq_bot_of_cycles_zero_not_one (H : Subgroup ASevenCertificateGroup)
    (hSH : a7S ≤ H) (hc : Cycles H (a7LocalFourgroup 0))
    (hnc : ¬ Cycles H (a7LocalFourgroup 1)) : a7U ⊓ H = ⊥ := by
  by_contra h
  exact hnc (a7_cycle_opposite_of_contains_U H hSH (a7U_le_of_inf_ne_bot H h) hc)

theorem a7_one_cycle_opposite_fixed_eq_bot (H : Subgroup ASevenCertificateGroup)
    (hSH : a7S ≤ H) (i j : Fin 2) (hij : i ≠ j)
    (hc : Cycles H (a7LocalFourgroup i)) (hnc : ¬ Cycles H (a7LocalFourgroup j)) :
    (a7U ⊓ Subgroup.centralizer (a7LocalFourgroup j : Set ASevenCertificateGroup)) ⊓ H = ⊥ := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · apply le_antisymm _ bot_le
    calc
      (a7U ⊓ Subgroup.centralizer (a7LocalFourgroup 1 : Set ASevenCertificateGroup)) ⊓ H
          ≤ a7U ⊓ H := inf_le_inf_right H inf_le_left
      _ = ⊥ := a7U_inf_eq_bot_of_cycles_zero_not_one H hSH hc hnc
  · change (a7U ⊓ Subgroup.centralizer (a7LocalFourgroup 0 : Set ASevenCertificateGroup)) ⊓ H = ⊥
    rw [a7U_fixedBy_zero_eq_bot, bot_inf_eq]
  · exact (hij rfl).elim

end CFSG.DihedralBlueprint
