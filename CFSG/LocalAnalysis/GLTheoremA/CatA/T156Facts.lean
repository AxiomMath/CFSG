module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def T156FactOmega (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S A : Subgroup Ω) (b : Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (PSimple p S) → A ≤ Subgroup.normalizer (S : Set Ω) → IsElemAbelian p A → b ∈ A →
    R2Prop p b S → (p = 3 → IsTD4 3 S → centCard2 3 S b = Nat.sqrt (card2 3 S)) →
    p ^ 3 * Nat.card ↥(A ⊓ centModSubgroup p S) ≤ Nat.card A →
    (∀ c ∈ A, NonInnDiag p c S → FieldOn p c S ∨ (p = 3 ∧ IsTD4 3 S)) →
    (Ipart p S b ≠ ⊥ ∧
        (∀ c ∈ A, CentMod p (Ipart p S b) c ↔ c ∈ Subgroup.zpowers b ⊔ (A ⊓ centModSubgroup p S)) ∧
        InnDiagOn p A (Ipart p S b)) ∨
      (p = 3 ∧ catalogIs (PSimple 3 S) S9.isU3eight)

end CFSG.LocalAnalysis.GLTheoremA.T156

end
