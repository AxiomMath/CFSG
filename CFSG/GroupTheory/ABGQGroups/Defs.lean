module

public import CFSG.GroupTheory.QuasiDihedralFusion.Defs
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.ABGQGroups

open CFSG.QuasiDihedralFusion

universe u

@[expose] def HasNormalSL2 (K : Type u) [Group K] (q : ℕ) : Prop :=
  ∃ (L : Subgroup K) (F : Type) (_ : Field F) (_ : Finite F),
    L.Normal ∧ Nat.card F = q ∧ Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F)

@[expose] def HasQCharPower (K : Type u) [Group K] (q : ℕ) : Prop :=
  IsQGroup K ∧ Odd q ∧ HasNormalSL2 (K ⧸ CFSG.oddCore K) q

@[expose] def HasQDCharPower (K : Type u) [Group K] (q : ℕ) : Prop :=
  IsQDGroup K ∧ ∀ y : K, orderOf y = 2 → HasQCharPower (Subgroup.centralizer ({y} : Set K)) q

end CFSG.ABGQGroups
