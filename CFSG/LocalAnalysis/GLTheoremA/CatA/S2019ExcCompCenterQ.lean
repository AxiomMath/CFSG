module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcRee

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def S2019ExcCompCenterQ : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      catalogIs K (onLie fun d => d.characteristic = q ∧ S2019ExcCoreIdx d) →
      ∀ β : MulAut K, β ^ p = 1 → β ≠ 1 → ∀ J : Subgroup K,
        GLAPComponent p (fixSubgroup β) J → q ∣ Nat.card (Subgroup.center ↥J) →
          (q = 3 ∧ catalogIs (↥J ⧸ Subgroup.center ↥J)
            (onLie fun d => d.characteristic = 3 ∧ d.fieldOrder = 3)) ∨
          catalogIs (↥J ⧸ Subgroup.center ↥J) (ambiguousChev q)

end CFSG.LocalAnalysis.GLTheoremA.S2019
