module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInInputs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Child

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage0

@[expose] def HypSplit (G : Type) [Group G] [Finite G] (L : Subgroup G) : Eps → Prop
  | .plus => Hyp7 G L
  | .minus => Hyp9 G L

@[expose] def SplitShape {G : Type} [Group G] (t : G) (L H₀ : Subgroup G) (x₀ : G) : Prop :=
  (ShapeC t L x₀ ∧ H₀ = L ⊔ zpowers x₀) ∨ ∃ r, ShapeD t L x₀ r ∧ H₀ = L ⊔ zpowers r ⊔ zpowers x₀

@[expose] def Sp6Kill (ε : Eps) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L H₀ U Q P : Subgroup G) (a : G) (ψ : V6 → G)
    (p u : Fin 6 → G) (x₀ : G), HypSplit G L ε → StepK t L → SplitShape t L H₀ x₀ →
      Inputs ε t L H₀ U Q P a ψ p u x₀ → (∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0) → False

@[expose] def Kill64 (ε : Eps) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L H₀ U Q P : Subgroup G) (a : G) (ψ : V6 → G)
    (p u : Fin 6 → G) (x₀ : G), HypSplit G L ε → StepK t L → SplitShape t L H₀ x₀ →
      Inputs ε t L H₀ U Q P a ψ p u x₀ → (∀ v, v ∈ Zset t Q ψ) → False

theorem endgameC7_of (h6 : Sp6Kill .plus) (h64 : Kill64 .plus) : EndgameC7 := by
  intro G _ _ L t b hH hK hC
  obtain ⟨m, hm, hC', U, Q, P, a, ψ, p, u, hI⟩ := exists_inputs_c_plus hK hH.2.1 hH.2.2 hC
  have hsh : SplitShape t L (L ⊔ zpowers b) (b * m) :=
    Or.inl ⟨hC', (sup_zpowers_mul_eq hm).symm⟩
  rcases hI.Zset_cases_plus hH.1.simple hH.1.nonab with h | h
  · exact h6 G t L _ U Q P a ψ p u _ hH hK hsh hI h
  · exact h64 G t L _ U Q P a ψ p u _ hH hK hsh hI h

theorem endgameD7_of (h6 : Sp6Kill .plus) (h64 : Kill64 .plus) : EndgameD7 := by
  intro G _ _ L t b r hH hK hD
  obtain ⟨m, hm, hD', U, Q, P, a, ψ, p, u, hI⟩ := exists_inputs_d_plus hK hH.2.1 hH.2.2 hD
  have hsh : SplitShape t L (L ⊔ zpowers r ⊔ zpowers b) (b * m) :=
    Or.inr ⟨r, hD', (sup_zpowers_mul_eq (mem_sup_left hm : m ∈ L ⊔ zpowers r)).symm⟩
  rcases hI.Zset_cases_plus hH.1.simple hH.1.nonab with h | h
  · exact h6 G t L _ U Q P a ψ p u _ hH hK hsh hI h
  · exact h64 G t L _ U Q P a ψ p u _ hH hK hsh hI h

theorem endgameC9_of (h6 : Sp6Kill .minus) (h64 : Kill64 .minus) : EndgameC9 := by
  intro G _ _ L t b hH hK hC
  obtain ⟨m, hm, hC', U, Q, P, a, ψ, p, u, hI⟩ := exists_inputs_c_minus hK hH.2.2 hC
  have hsh : SplitShape t L (L ⊔ zpowers b) (b * m) :=
    Or.inl ⟨hC', (sup_zpowers_mul_eq hm).symm⟩
  rcases hI.Zset_cases_minus hH.1.simple hH.1.nonab with h | h
  · exact h6 G t L _ U Q P a ψ p u _ hH hK hsh hI h
  · exact h64 G t L _ U Q P a ψ p u _ hH hK hsh hI h

end CFSG.EvenSmallLie.OmegaEight.SplitIn
