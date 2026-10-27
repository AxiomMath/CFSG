module

public import CFSG.CGT.T75N.L29Lift
public import CFSG.LieType.Steinberg.CentralExt.SLMilnor

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups
open CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

theorem not_perfect_of_card_six {Q : Type*} [Group Q] (h : Nat.card Q = 6) :
    ¬ Group.IsPerfect Q := by
  intro hperf
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [h]; norm_num)
  have hN : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hN, h] at this
    omega
  have hle : commutator Q ≤ Subgroup.zpowers x := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have key : ⁅a, b⁆ = a * b * (a⁻¹ * b⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [key, Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
  have htop : Subgroup.zpowers x = ⊤ := top_le_iff.mp (hperf.commutator_eq_top ▸ hle)
  have hcard := congrArg (fun H : Subgroup Q => Nat.card H) htop
  simp only [Subgroup.card_top, hN, h] at hcard
  omega

theorem false_of_perfect_sl_two_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {Y : Type} [Group Y] [Group.IsPerfect Y] (π : Y →* SpecialLinearGroup (Fin 2) F)
    (hπ : Function.Surjective π) : False := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := π) hπ
  have : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) F) = 6 := by
    rw [Matrix.card_SL_field 2, ← Nat.card_eq_fintype_card, hF]
    simp [Fin.prod_univ_two]
  exact not_perfect_of_card_six hcard hperf

theorem ker_eq_bot_of_generic
    {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hgen : (m = 0 ∧ 8 ≤ Nat.card F) ∨ (m = 1 ∧ 8 ≤ Nat.card F) ∨ (m = 2 ∧ 4 ≤ Nat.card F) ∨
      3 ≤ m)
    {Y : Type} [Group Y] [Group.IsPerfect Y]
    (π : Y →* SpecialLinearGroup (Fin (m + 2)) F) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center Y) : π.ker = ⊥ := by
  have hev : Even (Nat.card F) := even_card_of_pow (F := F) (V := F) (n := 1) one_ne_zero (by simp)
  have hq3 : Nat.card F ≠ 3 := fun h => by
    rw [h] at hev
    exact absurd hev (by decide)
  have hq9 : Nat.card F ≠ 9 := fun h => by
    rw [h] at hev
    exact absurd hev (by decide)
  have hsec : ∃ s : SpecialLinearGroup (Fin (m + 2)) F →* Y, ∀ g, π (s g) = g := by
    rcases hgen with ⟨rfl, h8⟩ | ⟨rfl, h8⟩ | ⟨rfl, h4⟩ | h3
    · exact SL2Closed.sl2_exists_section_of_central (k := F) (by omega) hq9 hπ hcen
    · exact SLClosed.sl_exists_section_of_central (m := 2) (by omega) (by omega) hπ hcen
    · refine SLClosed.sl_exists_section_of_separating (m := 3) (by omega)
        (SLClosed.separating_of_card (by omega) (by omega) (by omega) (by omega)) hπ hcen
    · exact SLClosed.sl_exists_section_of_four_le (m := m + 1) (by omega) hπ hcen
  obtain ⟨s, hs⟩ := hsec
  exact SL2Closed.ker_eq_bot_of_section π hcen s hs

end CFSG.CGT.T75N
