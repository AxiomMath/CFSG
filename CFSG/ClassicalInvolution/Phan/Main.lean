module

public import CFSG.ClassicalInvolution.Phan.Universal
public import CFSG.ClassicalInvolution.Phan.SimplyConnected
public import CFSG.ClassicalInvolution.Phan.Recognition

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.Assembly.LowTwoRank

theorem phanUniversal : PhanUniversal :=
  phanUniversal_of_simplyTwoConnected fun _ _ _ _ _ _ _ hK hq n _ =>
    frameSystem_simplyTwoConnected (isUnitaryInvolution_unitaryInvolution hK) hK (by omega) n

theorem weakPhan_recognition (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA K p f n U W) :
    ∃ θ : Su K p f (n + 1) →* X, Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center (Su K p f (n + 1)) :=
  weakPhan_odd_central_quotient_assembly phanUniversal K p f hK hq hn hW

theorem weakPhan_simple_native_recognition (K : Type) [Field K] [Finite K] (p f : ℕ)
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA K p f n U W) :
    StatedClassicalModel X .PSU (n + 1) p f ∧ Blueprint.OddLieType X :=
  weakPhan_odd_simple_native_recognition phanUniversal K p f hK hp hq hn hX hW

end CFSG.ClassicalInvolution.Phan
