module

public import CFSG.ClassicalInvolution.Phan.Assembly
public import CFSG.ClassicalInvolution.Phan.NativeModel
public import CFSG.Open.StatedDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.Assembly.LowTwoRank

theorem weakPhan_odd_central_quotient_assembly (hU : PhanUniversal) (K : Type) [Field K] [Finite K]
    (p f : ℕ) [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA K p f n U W) :
    ∃ θ : Su K p f (n + 1) →* X, Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center (Su K p f (n + 1)) :=
  weakPhan_of_phanUniversal hU K p f hK hq hn hW

theorem stated_psu_iff_open (G : Type) [Group G] (n p f : ℕ) :
    StatedClassicalModel G .PSU n p f ↔ CFSG.Open.StatedClassicalModel G .PSU n p f :=
  Iff.rfl

theorem weakPhan_odd_simple_native_recognition (hU : PhanUniversal) (K : Type) [Field K]
    [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X}
    (hW : WeakPhanA K p f n U W) :
    StatedClassicalModel X .PSU (n + 1) p f ∧ Blueprint.OddLieType X := by
  obtain ⟨θ, hθ, hker⟩ := weakPhan_odd_central_quotient_assembly hU K p f hK hq hn hW
  obtain ⟨-, -, hmodel, hodd⟩ :=
    unitary_simple_central_quotient_native_model K p f hK hp hn hX θ hθ hker
  refine ⟨?_, hodd⟩
  rcases hmodel with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  all_goals exact absurd h0 (Nat.succ_ne_zero n)

end CFSG.ClassicalInvolution.Phan
