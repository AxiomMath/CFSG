module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB

@[expose] def I114FactA : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nat.card (Subgroup.center K) = 3 →
    catalogIs (K ⧸ Subgroup.center K) S9.isL3char2 →
    ∃ y : K, (∃ z : K, z * y ≠ y * z) ∧ orderOf y = 3 ∧
      ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ y ∈ Subgroup.normalizer (U : Set K)

@[expose] def I114FactB : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSLThreeExc K →
    catalogIs (K ⧸ Subgroup.center K) S9.isL3char2 →
    ∀ (H : Subgroup (MulAut K)) (S : Subgroup K), IsElemAbelian 3 H → Nat.card H = 9 →
      S ≠ ⊥ → IsPGroup 2 S → (∀ h ∈ H, S.map (MulEquiv.toMonoidHom h) = S) →
      ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ h ∈ H, U.map (MulEquiv.toMonoidHom h) = U) ∧
        ∃ y : K, (∃ z : K, z * y ≠ y * z) ∧ orderOf y = 3 ∧
          y ∈ Subgroup.normalizer (U : Set K) ∧ (∀ h ∈ H, h y = y) ∧
          ∃ α ∈ H, orderOf α = 3 ∧ ¬ ∃ k : K, ∀ z : K, α z = k * z * k⁻¹

@[expose] def I114FactC : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nat.card (Subgroup.center K) = 3 →
    catalogIs (K ⧸ Subgroup.center K) S9.isL3char2 →
    (IsLTwoOddPow K ∨ IsHatSix K ∨ IsHatSeven K ∨ IsHatMTwentyTwo K ∨ IsSLThreeExc K ∨
      IsSUThreeExc K) →
    IsSLThreeExc K

end CFSG.LocalAnalysis.GLTheoremA.I114
