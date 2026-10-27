module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open Module

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem prime_le_four_of_dvd_card_linearEquiv (hW : finrank (ZMod 2) W = 2) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (W ≃ₗ[ZMod 2] W)) : p ≤ 4 := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ι : (W ≃ₗ[ZMod 2] W) →* Equiv.Perm W :=
    MonoidHom.mk' (fun g => g.toEquiv) (fun _ _ => rfl)
  have hinj : Function.Injective ι := fun g h hgh => LinearEquiv.ext fun w => Equiv.congr_fun hgh w
  have h1 := dvd_trans hdvd (Subgroup.card_dvd_of_injective ι hinj)
  rw [Nat.card_perm, ← FiniteField.pow_finrank_eq_natCard 2 W, hW] at h1
  exact (Nat.Prime.dvd_factorial hp).1 h1

theorem isSolvable_linearEquiv_of_finrank_two (hW : finrank (ZMod 2) W = 2) :
    Group.IsSolvable (W ≃ₗ[ZMod 2] W) := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  haveI : Finite (W ≃ₗ[ZMod 2] W) := Finite.of_injective (fun g : W ≃ₗ[ZMod 2] W => (g : W → W)) DFunLike.coe_injective
  refine CFSG.ComponentClassification.Burgoyne.C.isSolvable_of_prime_dvd_two_three fun p hp hdvd => ?_
  have := prime_le_four_of_dvd_card_linearEquiv hW hp hdvd
  interval_cases p <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hp (by norm_num)

theorem eq_one_of_pow_eq_one_of_finrank_two (hW : finrank (ZMod 2) W = 2) {g : W ≃ₗ[ZMod 2] W} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g ^ p = 1) : g = 1 := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  haveI : Finite (W ≃ₗ[ZMod 2] W) := Finite.of_injective (fun g : W ≃ₗ[ZMod 2] W => (g : W → W)) DFunLike.coe_injective
  have hord : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hg
  rcases (Nat.dvd_prime hp).1 hord with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    have := prime_le_four_of_dvd_card_linearEquiv hW hp (h ▸ orderOf_dvd_natCard g)
    omega

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
