module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcRee

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def CompNormal {S : Type*} [Group S] (β : MulAut S) : Prop :=
  ∀ J : Subgroup S, CFSG.Open.IsComponentOf J (fixSubgroup β) →
    fixSubgroup β ≤ Subgroup.normalizer (J : Set S)

@[expose] def IsE6Eps (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ Q : TauCeti.PrimePower, d = .E6 Q ∨ d = .twistedE6 Q

@[expose] def GenNormalExcInner : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie p T d →
    S2019.S2019ExcCoreIdx d.1 → ¬ (p = 3 ∧ IsE6Eps d.1) → ∀ x : MulAut T, x ^ p = 1 → x ≠ 1 →
      x ∈ innAutDerived T → CompNormal x

@[expose] def GenNormalExcOuter : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie p T d →
    S2019.S2019ExcCoreIdx d.1 → ∀ x : MulAut T, x ^ p = 1 → x ≠ 1 →
      x ∉ innAutDerived T → CompNormal x

@[expose] def GenPlaneE6Three : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie 3 T d →
    IsE6Eps d.1 → ∀ P : Subgroup (MulAut T), IsElemAbelian 3 P → Nat.card P = 3 ^ 2 →
      ∀ J : Subgroup T, ¬ ∀ x ∈ P, x ≠ 1 → GLAPComponent 3 (fixSubgroup x) J

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
