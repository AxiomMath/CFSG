module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResHeisLinear
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem linear_three_mem_linearAut {K : Type} [Field K] [Finite K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {X : Type} [Group X] [Finite X]
    (hrk : CFSG.LieType.SeitzGeneration.RankLE2 3 X)
    (ψ : X →* MulAut (projectiveSL 3 K)) (hψ : Function.Injective ψ) (L : Subgroup X)
    (hL : ∀ y : projectiveSL 3 K, ∃ l ∈ L, ψ l = MulAut.conj y) {x : X} (hx : x ^ 3 = 1) :
    ψ x ∈ linearAutGroup 3 K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hD
  have hn3 : 3 ≤ 3 := le_rfl
  set a : MulAut (projectiveSL 3 K) := ψ x with ha
  have hap : a ^ 3 = 1 := by rw [ha, ← map_pow, hx, map_one]
  have ha1 : a ≠ 1 := fun h => hD (h ▸ (linearAutGroup 3 K).one_mem)
  have hao : orderOf a = 3 := orderOf_eq_prime hap ha1
  have haE : a ∈ semilinearAutGroup 3 K :=
    mem_semilinearAutGroup_of_pow_odd hn3 (by decide : Odd 3) hap
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  obtain ⟨-, σ, hσo, ⟨h, hh, hah⟩, -⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      (K := K) (n := 3) (ℓ := 2) (f := (m : ℕ)) Nat.prime_two m.pos hn3 hcard Nat.prime_three a
      haE hD hao
  have hσ3 : σ ^ 3 = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
  have hσω : σ ω = ω := ringEquiv_apply_eq_of_pow_three hω hσ3
  obtain ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩ := exists_heisenberg_pair_linear hω σ hσω
  have hfix : ∀ y : projectiveSL 3 K, fieldAut 3 K σ y = y → ψ x (h y) = h y := by
    intro y hy
    have : ψ x = h * fieldAut 3 K σ * h⁻¹ := hah
    rw [this]
    simp [MulAut.mul_apply, hy]
  have hxout : ψ x ∉ inner (projectiveSL 3 K) := fun hin =>
    hD ((standard_outer_quotients (n := 3) (K := K)).1 hin)
  refine false_of_outer_fixing_pair Nat.prime_three
    (CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL hn3) hrk ψ hψ L hL hx hxout
    (y₁ := h x₁) (y₂ := h x₂) (hc.map h) ?_ ?_ ?_ (hfix x₁ hf1) (hfix x₂ hf2)
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · intro i j hij
    rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    exact hi i j (h.injective (hij.trans (map_one h).symm))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
