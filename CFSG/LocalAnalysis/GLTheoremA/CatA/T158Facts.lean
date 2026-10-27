module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBetaK

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure T158InnFactOmega (p : ℕ) : Prop where
  inn : p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x₁ x₂ : Ω) (L₁ L₂ : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    CFSG.Open.IsCatalogGroup (PSimple p S) →
    x₁ ^ p = 1 → x₂ ^ p = 1 → x₁ * x₂ = x₂ * x₁ →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁ → catalogIs (PSimple p L₁) S9.isU3eight →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x₂} : Set Ω)) L₂ → catalogIs (PSimple p L₂) S9.isU3eight →
    FieldOn p x₁ L₂ → FieldOn p x₂ L₁ →
    InnDiagOn p (Subgroup.zpowers x₁) S ∧ InnDiagOn p (Subgroup.zpowers x₂) S
  fg : p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x y : Ω) (J : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple 2 (PSimple p S) →
    x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ∉ Subgroup.zpowers y → y ∉ Subgroup.zpowers x →
    InnDiagOn p (Subgroup.zpowers x) S → FieldOn p y S →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J → y ∈ Subgroup.normalizer (J : Set Ω) →
    FGOn p y J

end CFSG.LocalAnalysis.GLTheoremA.T158

end
