module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112Ctx
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB

@[expose] def I114CoreSL : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), 1 ≤ f → Nat.card F = 2 ^ f → ¬ 3 ∣ f →
    (Nat.card F % 9 = 4 ∨ Nat.card F % 9 = 7) →
    ∀ (H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F)))
      (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)),
      IsElemAbelian 3 H → Nat.card H = 9 → S ≠ ⊥ → IsPGroup 2 S →
      (∀ h ∈ H, S.map (MulEquiv.toMonoidHom h) = S) →
      ∃ U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        (∀ h ∈ H, U.map (MulEquiv.toMonoidHom h) = U) ∧
        ∃ y : Matrix.SpecialLinearGroup (Fin 3) F, (∃ z, z * y ≠ y * z) ∧ orderOf y = 3 ∧
          y ∈ Subgroup.normalizer (U : Set (Matrix.SpecialLinearGroup (Fin 3) F)) ∧
          (∀ h ∈ H, h y = y) ∧
          ∃ α ∈ H, orderOf α = 3 ∧ ¬ ∃ k, ∀ z, α z = k * z * k⁻¹

end CFSG.LocalAnalysis.GLTheoremA.I114
