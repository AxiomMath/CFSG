module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.HardMathSupport.Timmesfeld.Balance.Alt

private theorem conj_injective_alternatingGroup_six :
    Function.Injective
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun e : MulAut (alternatingGroup (Fin 6)) => e h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc h * g = g * h * g⁻¹ * g := by rw [this]
      _ = g * h := by group
  rw [alternatingGroup.center_eq_bot (by simp)] at hc
  exact hc

private theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem dvd_card_mulAut_alternatingGroup_six :
    360 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
  obtain ⟨hfin, -⟩ := finite_and_card_mulAut_alternatingGroup_six_le
  have h := Subgroup.card_subgroup_dvd_card
    (MonoidHom.range (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))))
  rwa [← Nat.card_congr
      (MonoidHom.ofInjective conj_injective_alternatingGroup_six).toEquiv,
    card_alternatingGroup_six] at h

theorem no_elemAbelian_square_mulAut_alternating_six
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (D : Subgroup (MulAut (alternatingGroup (Fin 6)))) :
    ¬ (IsMulCommutative D ∧ (∀ x ∈ D, x ^ p = 1) ∧ Nat.card D = p ^ 2) := by
  rintro ⟨-, -, hD⟩
  obtain ⟨hfin, hle⟩ := finite_and_card_mulAut_alternatingGroup_six_le
  have h1 : p ^ 2 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    rw [← hD]
    exact Subgroup.card_subgroup_dvd_card D
  obtain ⟨j, hj⟩ := dvd_card_mulAut_alternatingGroup_six
  rw [hj] at h1 hle
  have hj4 : j ≤ 4 := by omega
  have hcop : Nat.Coprime (p ^ 2) 360 := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have : p ≤ 360 := Nat.le_of_dvd (by norm_num) h
    have h360 : (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 := by norm_num
    rw [h360] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h5 | h5
    · rcases (Nat.Prime.dvd_mul hp).1 h5 with h6 | h6
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h6)
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h6)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h6)
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
      omega
  have h2 : p ^ 2 ∣ j := hcop.dvd_of_dvd_mul_left h1
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      have := Nat.card_pos (α := MulAut (alternatingGroup (Fin 6)))
      omega
    · exact h
  have := Nat.le_of_dvd hjpos h2
  nlinarith

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
