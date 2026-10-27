module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def heartZVec : Fin 8 → ZMod 2 := fun i => if (i : ℕ) < 4 then 1 else 0

@[expose] def IsFirstBlockVec (v : Fin 8 → ZMod 2) : Prop :=
  IsEvenVec v ∧ ∀ i : Fin 8, 4 ≤ (i : ℕ) → v i = 0

@[expose] def IsSecondBlockVec (v : Fin 8 → ZMod 2) : Prop :=
  IsEvenVec v ∧ ∀ i : Fin 8, (i : ℕ) < 4 → v i = 0

@[expose] def Asc82HeartDict : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∃ (Alt : Subgroup (Equiv.Perm (Fin 8))) (φ : (Fin 8 → ZMod 2) → G),
        (Alt = alternatingGroup (Fin 8) ∨ Alt = ⊤) ∧
        IsPermModuleMod (n := 8) IsEvenVec ({0, fun _ => 1} : Set (Fin 8 → ZMod 2)) φ A ⊥
          (normalizer (A : Set G)) Alt ∧
        z = φ heartZVec ∧
        (∀ x : G, x ∈ A ⊓ (K₁ ⊔ K₂) ↔ ∃ v, IsFirstBlockVec v ∧ φ v = x) ∧
        (∀ x : G, x ∈ A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) ↔
          ∃ v, IsSecondBlockVec v ∧ φ v = x)

end CFSG.OddStandard.SmallF3.Omega
