module

public import CFSG.CharacterTheory.Semidihedral.ExchangedEigensubgroups
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoPrimeOrderSolvability

public section

namespace CFSG.Wreathed.ExchangedEigensubgroupFive

open CFSG.Semidihedral CFSG.Semidihedral.ExchangedEigensubgroups

universe u v w

theorem card_GL_two_three : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

theorem isSolvable_GL_two_three : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
  CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable _ 2 3 Nat.prime_two Nat.prime_three
    fun r hr hdvd => by
      rw [card_GL_two_three, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at hdvd
      rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)

theorem eq_one_of_GL_two_three {J : Type w} [Group J] [Group.IsPerfect J]
    (τ : J →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (j : J) : τ j = 1 := by
  by_contra h
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := isSolvable_GL_two_three
  have : Group.IsPerfect τ.range := Group.IsPerfect.range τ
  have : Nontrivial τ.range := ⟨⟨⟨τ j, j, rfl⟩, 1, fun h' => h (congrArg Subtype.val h')⟩⟩
  exact Group.IsPerfect.not_isSolvable τ.range inferInstance

theorem prime_dvd_card_of_nontrivial {A : Type u} [Group A] [Finite A] [Nontrivial A] {ell : ℕ}
    (hell : ell.Prime) (hA : IsPGroup ell A) : ell ∣ Nat.card A := by
  have : Fact ell.Prime := ⟨hell⟩
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero, Nat.card_eq_one_iff_unique] at hk
    exact absurd hk.1 (not_subsingleton A)
  · rw [hk]
    exact dvd_pow_self ell (Nat.succ_ne_zero k)

variable {R : Type u} [CommGroup R]

theorem eigengroups_characteristic_eq_five [Finite R] [Nontrivial R]
    {F : Type v} [Field F] {J : Type w} [Group J] [Group.IsPerfect J]
    {p ell f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hell : ell.Prime) (hellodd : Odd ell)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq : p ^ f = 5)
    (ρ : J →* MulAut R) (t : J) (hinv : ∀ r : R, ρ t r = r⁻¹) (hR : IsPGroup ell R)
    (α : MulAut R) (hα : α ^ 2 = 1) (d : J)
    (hexchange : ρ d * α * (ρ d)⁻¹ = ρ t * α)
    (ι : positiveGroup α →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι) :
    ell = p := by
  by_contra hne
  have : Fact ell.Prime := ⟨hell⟩
  have hoddR := odd_card_of_odd_prime_group hell hellodd hR
  have he := exchange_identity ρ t d hinv α hexchange
  obtain ⟨hpnontrivial, hmnontrivial⟩ := eigengroups_nontrivial hoddR α hα (ρ d) he
  have : Nontrivial (positiveGroup α) := hpnontrivial
  have : Nontrivial (negativeGroup α) := hmnontrivial
  have hp5 : p = 5 := by
    have h : p ∣ p ^ f := dvd_pow_self p (by omega)
    rw [hq] at h
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
  have hS : Nat.card (OddProjectiveCoverKernel.S F) = 60 := by
    rw [(OddProjectiveCoverKernel.odd_projective_linear_two_Sylow_data F hp hpodd hf hF).2.1, hq]
    norm_num
  have hdvd : ell ∣ 60 := by
    have h₁ := prime_dvd_card_of_nontrivial hell (hR.to_subgroup (positiveGroup α))
    have h₂ : Nat.card (positiveGroup α) ∣ Nat.card (OddProjectiveCoverKernel.S F) := by
      rw [Nat.card_congr (ι.ofInjective hι).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    exact hS ▸ h₁.trans h₂
  have hell3 : ell = 3 := by
    rw [show (60 : ℕ) = 2 ^ 2 * (3 * 5) by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hell).mp hdvd with h | h
    · have h2 := (Nat.prime_dvd_prime_iff_eq hell Nat.prime_two).mp (hell.dvd_of_dvd_pow h)
      subst h2
      exact absurd hellodd (Nat.not_odd_iff_even.mpr even_two)
    · rcases (Nat.Prime.dvd_mul hell).mp h with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hell Nat.prime_three).mp h
      · exact absurd (((Nat.prime_dvd_prime_iff_eq hell Nat.prime_five).mp h).trans hp5.symm) hne
  subst hell3
  obtain ⟨hpcyclic, hmcyclic⟩ := eigengroups_nondefining_cyclic hp hpodd hf hF
    hell hellodd hne hR α (ρ d) he ι hι
  have : IsCyclic (positiveGroup α) := hpcyclic
  have : IsCyclic (negativeGroup α) := hmcyclic
  let e := eigenProductEquiv hoddR α hα
  have hτ := CyclicPairFrattini.matrixCoordinateAction_inversion_ne_one 3
    (hR.to_subgroup (positiveGroup α)) (hR.to_subgroup (negativeGroup α)) e hellodd ρ t hinv
  exact hτ (eq_one_of_GL_two_three _ t)

end CFSG.Wreathed.ExchangedEigensubgroupFive
