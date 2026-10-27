module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcRee

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def S2019ExcSecRank : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ (K : Type) [Group K] [Finite K],
    catalogIs K (onLie fun d => d.characteristic = q ∧ S2019ExcCoreIdx d ∧ ∀ Q, d ≠ .G2 Q) →
      CFSG.GH74.SectionalTwoRankLE K 17

@[expose] def S2019ExcCompNotRee : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (K : Type) [Group K] [Finite K],
      catalogIs K (onLie fun d => d.characteristic = q ∧ S2019ExcCoreIdx d) →
      ∀ β : MulAut K, β ^ p = 1 → ∀ J : Subgroup K, GLAPComponent p (fixSubgroup β) J →
        ¬ catalogIs (↥J ⧸ Subgroup.center ↥J) (onLie fun d => ∃ m, d = .reeG2 m)

@[expose] def S2019ChevSpecialQ : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (d : TauCeti.LieTypeIndex),
    catalogIs Y (onLie (· = d)) → d.characteristic = q → (∀ Q, d ≠ .A 1 Q) →
      (∀ m, d ≠ .reeG2 m) →
      ∃ R : Subgroup Y, IsPGroup q R ∧ (∀ r ∈ R, r ^ q = 1) ∧ Nat.card R = d.fieldOrder ^ 3 ∧
        Nat.card (Subgroup.center ↥R) = d.fieldOrder ∧
        ∀ (Z : Subgroup ↥R) [Z.Normal], Z ≤ Subgroup.center ↥R →
          Z.relIndex (Subgroup.center ↥R) = q → CFSG.IsExtraspecialPGroup q (↥R ⧸ Z)

@[expose] def S2019ChevOutThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (d : TauCeti.LieTypeIndex), catalogIs Y (onLie (· = d)) →
    d.characteristic = 3 → d.fieldOrder = 3 → (Nat.card Y).factorization 3 ≤ 10 →
      ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ α : MulAut Y, α ^ p = 1 → ∃ y : Y, α = MulAut.conj y

end CFSG.LocalAnalysis.GLTheoremA.S2019
