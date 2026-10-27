module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenAct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

@[expose] def ActData (p : ℕ) {Ω X : Type} [Group Ω] [Group X] (B : Subgroup Ω)
    (α : ↥B → MulAut X) : Prop :=
  ∃ (D E : Subgroup Ω) (J : Subgroup X) (t : X), D ≤ B ∧ E ≤ B ∧ D ≤ E ∧
    p ^ 2 ≤ Nat.card D ∧ p ^ 2 * Nat.card D ≤ Nat.card B ∧
    (Nat.card D = p ^ 2 → Nat.card E = p ^ 3) ∧
    GLAPComponent p (actFix α D) J ∧ (∀ x : ↥B, J.map (α x).toMonoidHom = J) ∧
    (∀ x : ↥B, (∀ j ∈ J, j * (α x j)⁻¹ ∈ GLAPPrimeCoreOf p J) → (x : Ω) ∈ D) ∧
    (Nat.card D = p ^ 2 → GLAPLayer p (J ⊓ actFix α E) ≠ ⊥) ∧
    t ≠ 1 ∧ t ^ 2 = 1 ∧ J ≤ Subgroup.centralizer ({t} : Set X) ∧
    ∀ x : ↥B, (x : Ω) ∈ D → α x t = t

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
