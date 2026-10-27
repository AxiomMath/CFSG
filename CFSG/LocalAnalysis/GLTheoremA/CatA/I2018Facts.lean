module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def I2018OddB3 : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ 2 → KDChevDownQ 3 r

@[expose] def I2018U38Char2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], catalogIs X CFSG.LocalAnalysis.GLTheoremA.S9.isU3eight →
    ∀ r : ℕ, IsChevSimple r X → r = 2

@[expose] def I2018U38NotAlt : Prop :=
  ∀ (X : Type) [Group X] [Finite X], catalogIs X CFSG.LocalAnalysis.GLTheoremA.S9.isU3eight →
    ∀ m : ℕ, 5 ≤ m → Nonempty (X ≃* alternatingGroup (Fin m)) → False

@[expose] def I2018U38Cover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    catalogIs (X ⧸ Subgroup.center X) CFSG.LocalAnalysis.GLTheoremA.S9.isU3eight →
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.IsL3Kind 2 X

@[expose] def I2018BorelTits : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsChevSimple 2 S →
    ∀ T : Subgroup S, IsPGroup 2 T → T ≠ ⊥ →
      ∃ P : Subgroup S, P ≠ ⊤ ∧ T ≤ pCoreOf 2 P ∧ Subgroup.normalizer (T : Set S) ≤ P

@[expose] def I2018ChevCore : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → IsChevSimple 2 S →
    ∀ α : MulAut S, α ^ 3 = 1 → ∀ P : Subgroup S, P ≠ ⊤ → ∀ T : Subgroup S, T ≤ pCoreOf 2 P → T ≠ ⊥ →
    ∀ J : Subgroup S, GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) J → J ≤ P →
      catalogIs (PSimple 3 J) CFSG.LocalAnalysis.GLTheoremA.S9.isU3eight →
      ¬ catalogIs S (onLie fun | .trialityD4 _ => True | _ => False) ∧
      ∃ lab : CFSG.Assembly.LargeEvenLabel, CFSG.Assembly.LargeEvenInLambda2 lab ∧
        ((lab.n = 1 ∧ 2 ^ 6 < twoPart (Nat.card S)) ∨ (lab.n = 3 ∧ 2 ^ 18 < twoPart (Nat.card S))) ∧
        CFSG.Assembly.LargeEvenRawDatum lab
          (fun R _ _ _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ Nonempty (S ≃* R))

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
