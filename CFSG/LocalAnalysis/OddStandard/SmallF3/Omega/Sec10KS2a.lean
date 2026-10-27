module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

theorem sl23_unique_involution (x : SL23) (hx : x * x = 1) : x = 1 ∨ x = -1 :=
  (by decide : ∀ y : SL23, y * y = 1 → y = 1 ∨ y = -1) x hx

@[expose] def sl23Q8 : Subgroup SL23 where
  carrier := {x | x ^ 4 = 1}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

theorem sl23Q8_normal : sl23Q8.Normal where
  conj_mem := by
    intro n hn g
    change (g * n * g⁻¹) ^ 4 = 1
    exact (by decide : ∀ n g : SL23, n ^ 4 = 1 → (g * n * g⁻¹) ^ 4 = 1) n g hn

theorem sl23Q8_isPGroup : IsPGroup 2 sl23Q8 :=
  fun g => ⟨2, Subtype.ext (by
    have hg : (g : SL23) ^ 4 = 1 := g.2
    simpa using hg)⟩

theorem sl23_q8_comm_sq (x y : SL23) (hx : x ^ 4 = 1) (hy : y ^ 4 = 1) :
    (x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = -1) ∧
      (x * x = 1 ∨ x * x = -1) :=
  (by decide : ∀ x y : SL23, x ^ 4 = 1 → y ^ 4 = 1 →
    (x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = -1) ∧
      (x * x = 1 ∨ x * x = -1)) x y hx hy

theorem sl23Q8_le_pCore : sl23Q8 ≤ CFSG.pCore 2 SL23 :=
  le_sSup ⟨sl23Q8_normal, sl23Q8_isPGroup⟩

theorem sl23_pCore_le_Q8 : CFSG.pCore 2 SL23 ≤ sl23Q8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card SL23 = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hdvd8 : Nat.card (CFSG.pCore 2 SL23) ∣ 8 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := SL23) (p := 2))
    have hdvd24 : 2 ^ n ∣ 24 := by
      have h := Subgroup.card_subgroup_dvd_card (CFSG.pCore 2 SL23)
      rw [hcard] at h
      exact hn ▸ h
    have hn3 : n ≤ 3 := by
      by_contra h
      push Not at h
      have h4 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have : 2 ^ 4 ∣ 24 := h4.trans hdvd24
      norm_num at this
    calc Nat.card (CFSG.pCore 2 SL23) = 2 ^ n := hn
      _ ∣ 2 ^ 3 := pow_dvd_pow 2 hn3
      _ = 8 := by norm_num
  intro x hx
  refine (by decide : ∀ y : SL23, y ^ 8 = 1 → y ^ 4 = 1) x ?_
  exact orderOf_dvd_iff_pow_eq_one.mp
    ((Subgroup.orderOf_dvd_natCard (CFSG.pCore 2 SL23) hx).trans hdvd8)

theorem sl23_pCore_eq_Q8 : CFSG.pCore 2 SL23 = sl23Q8 :=
  le_antisymm sl23_pCore_le_Q8 sl23Q8_le_pCore

theorem sl23_neg_one_mem_pCore : (-1 : SL23) ∈ CFSG.pCore 2 SL23 := by
  rw [sl23_pCore_eq_Q8]
  change (-1 : SL23) ^ 4 = 1
  decide

theorem mem_sl23Q8 (x : SL23) : x ∈ sl23Q8 ↔ x ^ 4 = 1 := Iff.rfl

theorem sl23_card_pCore : Nat.card (CFSG.pCore 2 SL23) = 8 := by
  letI : DecidablePred (· ∈ sl23Q8) := fun x =>
    decidable_of_decidable_of_iff (p := x ^ 4 = 1) (mem_sl23Q8 x).symm
  letI : Fintype sl23Q8 := Subtype.fintype (fun x : SL23 => x ∈ sl23Q8)
  rw [sl23_pCore_eq_Q8, Nat.card_eq_fintype_card]
  decide

end CFSG.OddStandard.SmallF3.Omega
