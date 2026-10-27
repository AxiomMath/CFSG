module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

structure U3TorusHyp (S : Type) [Group S] (labL : GLALabel) (β β₁ β₂ : MulAut S) (n : ℕ)
    (J : Subgroup S) : Prop where
  core : U3CoreHyp S labL β n J
  innDiagKind₁ : InnDiagKind S labL β₁
  innDiagKind₂ : InnDiagKind S labL β₂
  pow_three₁ : β₁ ^ 3 = 1
  pow_three₂ : β₂ ^ 3 = 1
  commute₁ : Commute β β₁
  commute₂ : Commute β β₂
  commute₁₂ : Commute β₁ β₂
  map_eq₁ : J.map β₁.toMonoidHom = J
  map_eq₂ : J.map β₂.toMonoidHom = J
  moves₁ : ∃ j ∈ J, β₁ j ≠ j
  moves₂ : ∀ k : ℕ, ∃ j ∈ J, (β₂ * β₁ ^ k) j ≠ j
  unique : ∀ J' : Subgroup S, IsComponentOf J' (fixSubgroup β) → J' = J

@[expose] def U3TorusCoreOn (Fam : GLALabel → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (labL : GLALabel) (β β₁ β₂ : MulAut S) (n : ℕ)
    (J : Subgroup S),
    Fam labL → U3TorusHyp S labL β β₁ β₂ n J →
      ¬ (IsSolvable ↥(J ⊓ fixSubgroup β₁) ∧ IsSolvable ↥(J ⊓ fixSubgroup β₂))

@[expose] def U3TorusCoreS : Prop := U3TorusCoreOn fun _ => True

theorem u3TorusCoreS_of_families (hL : U3TorusCoreOn FamLin) (hU : U3TorusCoreOn FamUni)
    (hSp : U3TorusCoreOn FamSymp) (hO : U3TorusCoreOn FamOrth) (hE : U3TorusCoreOn FamExc) :
    U3TorusCoreS := by
  intro S _ _ labL β β₁ β₂ n J _ h
  rcases fam_cover labL with hF | hF | hF | hF | hF
  · exact hL S labL β β₁ β₂ n J hF h
  · exact hU S labL β β₁ β₂ n J hF h
  · exact hSp S labL β β₁ β₂ n J hF h
  · exact hO S labL β β₁ β₂ n J hF h
  · exact hE S labL β β₁ β₂ n J hF h

theorem u3TorusCoreOn_of_false {Fam : GLALabel → Prop}
    (h : ∀ (S : Type) [Group S] [Finite S] (labL : GLALabel)
    (β : MulAut S) (n : ℕ) (J : Subgroup S), Fam labL → U3CoreHyp S labL β n J → False) :
    U3TorusCoreOn Fam := by
  intro S _ _ labL β β₁ β₂ n J hF hT
  exact (h S labL β n J hF hT.core).elim

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
