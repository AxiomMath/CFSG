module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDelta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private theorem Sec4MRealizes.pow {m : G} {σ : Equiv.Perm (Option (Fin 7))}
    (hσ : Sec4MRealizes t φ m σ) (n : ℕ) :
    Sec4MRealizes t φ (m ^ n) (σ ^ n) := by
  induction n with
  | zero => simpa using (Sec4MRealizes.one (t := t) (φ := φ))
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hσ

private theorem isThreeCycle_swap_mul_swap_of_share {a b a' b' : Option (Fin 7)}
    (hab : a ≠ b) (hab' : a' ≠ b') (hne : Equiv.swap a b ≠ Equiv.swap a' b')
    (hov : a = a' ∨ a = b' ∨ b = a' ∨ b = b') :
    Equiv.Perm.IsThreeCycle (Equiv.swap a b * Equiv.swap a' b') := by
  rcases hov with h | h | h | h
  · subst a'
    by_cases hbb' : b = b'
    · exact absurd (by rw [hbb']) hne
    · exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hab' hbb'
  · subst b'
    rw [Equiv.swap_comm a' a]
    have hba' : b ≠ a' := by
      intro hb
      exact hne (by rw [hb, Equiv.swap_comm a a'])
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hab (Ne.symm hab') hba'
  · subst a'
    rw [Equiv.swap_comm a b]
    have habv : a ≠ b' := by
      intro ha
      exact hne (by rw [ha, Equiv.swap_comm b' b])
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) hab' habv
  · subst b'
    rw [Equiv.swap_comm a b, Equiv.swap_comm a' b]
    have haa' : a ≠ a' := by
      intro ha
      exact hne (by rw [ha])
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) (Ne.symm hab') haa'

theorem Sec4FSetup.swap_overlap (h : Sec4FSetup t L S z A B φ) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) {y y' : G} (hy : y ∈ P) (hy' : y' ∈ P) {a b a' b' : Option (Fin 7)}
    (hab : a ≠ b) (hab' : a' ≠ b') (hσ : Sec4MRealizes t φ y (Equiv.swap a b))
    (hσ' : Sec4MRealizes t φ y' (Equiv.swap a' b'))
    (hov : a = a' ∨ a = b' ∨ b = a' ∨ b = b') : Equiv.swap a b = Equiv.swap a' b' := by
  by_contra hne
  have h3 : Equiv.Perm.IsThreeCycle (Equiv.swap a b * Equiv.swap a' b') :=
    isThreeCycle_swap_mul_swap_of_share hab hab' hne hov
  obtain ⟨k, hk⟩ := hP2 ⟨y * y', mul_mem hy hy'⟩
  have hpow : (y * y') ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hreal : Sec4MRealizes t φ 1 ((Equiv.swap a b * Equiv.swap a' b') ^ 2 ^ k) := by
    have hpk := (hσ.mul hσ').pow (2 ^ k)
    rw [hpow] at hpk
    exact hpk
  have hσk : (Equiv.swap a b * Equiv.swap a' b') ^ 2 ^ k = 1 :=
    Sec4MRealizes.unique h.pt_injective hreal Sec4MRealizes.one
  have hdvd : orderOf (Equiv.swap a b * Equiv.swap a' b') ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hσk
  rw [h3.orderOf] at hdvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
