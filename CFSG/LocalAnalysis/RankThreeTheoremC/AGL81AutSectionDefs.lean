module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.Open

@[expose] def HasSmallLinearModel (q : ℕ) (V : Type) [Group V] : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod q) W) (_ : Module.Finite (ZMod q) W),
    Module.finrank (ZMod q) W ≤ 4 ∧
    ∃ ρ : MulAut V →* (Module.End (ZMod q) W)ˣ,
      ∀ x : MulAut V, ρ x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1

@[expose] def SmallAutomizer (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ T : Sylow p K, IsMulCommutative (T : Subgroup K) ∧
    ∀ k ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
      (∀ t ∈ (T : Subgroup K), k ^ 3 * t * (k ^ 3)⁻¹ = t) ∨
        (∀ t ∈ (T : Subgroup K), k ^ 4 * t * (k ^ 4)⁻¹ = t)

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
