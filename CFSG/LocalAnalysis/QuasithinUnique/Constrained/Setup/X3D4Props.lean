module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3H13Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender

@[expose] def A6SimpleModules : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : alternatingGroup (Fin 6) →* (W ≃ₗ[ZMod 2] W)),
    IsLSimple σ ⊤ (⊤ : Submodule (ZMod 2) W) →
    (Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 4 ∨
      Module.finrank (ZMod 2) W = 16) ∧
    (Module.finrank (ZMod 2) W = 1 → ∀ g w, σ g w = w) ∧
    (Module.finrank (ZMod 2) W = 4 → ∀ R : Subgroup (alternatingGroup (Fin 6)), Nat.card R = 8 →
      Module.finrank (ZMod 2) (fixSub σ R) = 1)

@[expose] def A6ShortGeneration : Prop :=
  Nat.card (MulAut (alternatingGroup (Fin 6))) = 1440 ∧
  (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.index = 4 ∧
  (∀ a : alternatingGroup (Fin 6), a ≠ 1 → a * a = 1 →
    ∃ g : Fin 3 → alternatingGroup (Fin 6),
      Subgroup.closure (Set.range fun i => g i * a * (g i)⁻¹) = ⊤) ∧
  (∀ A : Subgroup (MulAut (alternatingGroup (Fin 6))), A ≠ ⊥ → CFSG.IsElementaryAbelian 2 ↥A →
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ s : Fin m → alternatingGroup (Fin 6),
        (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ≤
          Subgroup.closure (⋃ i, ((A.map (MulAut.conj (MulAut.conj (s i))).toMonoidHom :
            Subgroup (MulAut (alternatingGroup (Fin 6)))) : Set (MulAut (alternatingGroup (Fin 6))))))

end CFSG.QuasithinUnique.Setup.X3
