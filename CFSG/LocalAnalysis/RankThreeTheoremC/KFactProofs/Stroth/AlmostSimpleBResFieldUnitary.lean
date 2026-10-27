module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResHeisUnitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResUnitary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem unitary_three_mem_primeFormD {f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 f K)
    (hf : f ≠ 1) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hωb : hU.bar ω * ω = 1)
    (hconj : Function.Injective
      (MulAut.conj : primeFormP hU (idC K) →* MulAut (primeFormP hU (idC K))))
    {X : Type} [Group X] [Finite X] (hrk : CFSG.LieType.SeitzGeneration.RankLE2 3 X)
    (ψ : X →* MulAut (primeFormP hU (idC K))) (hψ : Function.Injective ψ) (L : Subgroup X)
    (hL : ∀ y : primeFormP hU (idC K), ∃ l ∈ L, ψ l = MulAut.conj y) {x : X} (hx : x ^ 3 = 1) :
    ψ x ∈ primeFormD hU (idC K) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 := hU.charP
  have hn3 : 3 ≤ 3 := le_rfl
  have hq : ¬ (3 = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h⟩
    exact hf (Nat.pow_right_injective (le_refl 2) (h.trans (pow_one 2).symm))
  by_contra hD
  set a : MulAut (primeFormP hU (idC K)) := ψ x with ha
  have hap : a ^ 3 = 1 := by rw [ha, ← map_pow, hx, map_one]
  have ha1 : a ≠ 1 := fun h => hD (h ▸ (primeFormD hU (idC K)).one_mem)
  have hao : orderOf a = 3 := orderOf_eq_prime hap ha1
  have hker := ker_primeFormFieldFactor hU (isPrimeFormGram_one_three (K := K)) hn3 hq
  set σ : K ≃+* K := primeFormFieldFactor hU (isPrimeFormGram_one_three (K := K)) hn3 hq a
    with hσdef
  have hσ1 : σ ≠ 1 := fun h => hD (by
    rw [← hker]
    exact h)
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hap, map_one]
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' hU hn3 hq
      Nat.prime_three (by norm_num) a hao σ rfl hσo
  set h' : MulAut (primeFormP hU (idC K)) := primeFormConjHom hU (idC K) M with hh'
  have hah : a = h' * primeFormFieldHom hU (isPrimeFormGram_one_three (K := K)) σ * h'⁻¹ := by
    calc a = h' * (h'⁻¹ * a * h') * h'⁻¹ := by group
      _ = h' * primeFormFieldHom hU (isPrimeFormGram_one_three (K := K)) σ * h'⁻¹ := by rw [hM]
  have hσω : σ ω = ω := ringEquiv_apply_eq_of_pow_three hω hσ3
  obtain ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩ := exists_heisenberg_pair_unitary hU hω hωb σ hσω
  have hfix : ∀ y : primeFormP hU (idC K),
      primeFormFieldHom hU (isPrimeFormGram_one_three (K := K)) σ y = y → ψ x (h' y) = h' y := by
    intro y hy
    have : ψ x = h' * primeFormFieldHom hU (isPrimeFormGram_one_three (K := K)) σ * h'⁻¹ := hah
    rw [this]
    simp [MulAut.mul_apply, hy]
  have hxout : ψ x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP hU (idC K)) := by
    intro hin
    obtain ⟨s, hs⟩ := (mem_inner_primeFormP hU (idC K) _).1 hin
    exact hD ⟨⟨s, s.2.1⟩, hs.symm⟩
  refine false_of_outer_fixing_pair Nat.prime_three hconj hrk ψ hψ L hL hx hxout
    (y₁ := h' x₁) (y₂ := h' x₂) (hc.map h') ?_ ?_ ?_ (hfix x₁ hf1) (hfix x₂ hf2)
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · intro i j hij
    rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    exact hi i j (h'.injective (hij.trans (map_one h').symm))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
