module

public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof

theorem six_le_finrank_of_card_eq_27_aux1 (d : ℕ) (hd : d ≤ 5) :
    ¬ 27 ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  interval_cases d <;> simp [Fin.prod_univ_succ]

theorem six_le_finrank_of_card_eq_27 {H : Type*} [Group H] {X : Type*} [AddCommGroup X]
    [Module (ZMod 2) X] [Finite X] (f : H →* (Module.End (ZMod 2) X)ˣ)
    (hf : Function.Injective f) {P : Subgroup H} (hP : Nat.card P = 27) :
    6 ≤ Module.finrank (ZMod 2) X := by
  classical
  haveI : FiniteDimensional (ZMod 2) X := Module.Finite.of_finite
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hdvd : 27 ∣ Nat.card (X ≃ₗ[ZMod 2] X) := by
    have h1 : Nat.card (P.map f) = 27 := by rw [Subgroup.card_map_of_injective hf, hP]
    have h2 := Subgroup.card_subgroup_dvd_card (P.map f)
    rw [h1, Nat.card_congr
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) X).toEquiv] at h2
    exact h2
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank (ZMod 2) X = d := ⟨_, rfl⟩
  rw [CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod hd] at hdvd
  exact six_le_finrank_of_card_eq_27_aux1 d (by omega) hdvd

theorem six_le_finrank_of_dvd_27 {H : Type*} [Group H] {X : Type*} [AddCommGroup X]
    [Module (ZMod 2) X] [Finite X] (f : H →* (Module.End (ZMod 2) X)ˣ)
    (hf : Function.Injective f) (h27 : 27 ∣ Nat.card H) :
    6 ≤ Module.finrank (ZMod 2) X := by
  classical
  haveI : Finite (X ≃ₗ[ZMod 2] X) :=
    Finite.of_injective (fun e : X ≃ₗ[ZMod 2] X => (e : X → X)) DFunLike.coe_injective
  haveI : Finite (Module.End (ZMod 2) X)ˣ :=
    Finite.of_equiv _ (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) X).toEquiv.symm
  haveI : Finite H := Finite.of_injective f hf
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 3) (by simpa using h27)
  exact six_le_finrank_of_card_eq_27 f hf (P := P) (by simpa using hP)

end CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof
