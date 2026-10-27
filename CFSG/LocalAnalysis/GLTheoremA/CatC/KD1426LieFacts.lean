module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD2027

public section

open CFSG.Open
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.KD2027Aux
open CFSG.HardMathSupport.Solomon.Coordinator

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

@[expose] def L3AutFourFacts : Prop :=
  ∀ (S : Type) [Group S] [Finite S], L3Model S → ∀ A : Subgroup (MulAut S), IsElemAbelian 3 A →
    (∀ α ∈ A, α ≠ 1 → GLAPLayer 3 (fixSubgroup α) = ⊥) →
    Nat.card A ≤ 9 ∧ (Nat.card A = 9 → ∃ T : Subgroup S, IsElemAbelian 2 T ∧ Nat.card T = 4 ∧
      (∀ α ∈ A, T.map α.toMonoidHom = T) ∧ ∃ α ∈ A, ∀ t ∈ T, ∃ s ∈ T, t = α s * s⁻¹)

@[expose] def L3AutFieldFacts : Prop :=
  ∀ (S : Type) [Group S] [Finite S], L3Model S → ∀ A : Subgroup (MulAut S), IsElemAbelian 3 A →
    27 ≤ Nat.card A → ∃ α ∈ A, α ≠ 1 ∧
      GLAPComponent 3 (fixSubgroup α) (GLAPLayer 3 (fixSubgroup α)) ∧
      catalogIs ↥(GLAPLayer 3 (fixSubgroup α)) (onLie k3Lie)

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie
