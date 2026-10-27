module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG

@[expose] def N2Cfg (Y : Type) [Group Y] (r : ℕ) (V Z : Subgroup (MulAut Y)) : Prop :=
  r.Prime ∧ Odd r ∧ IsElementaryAbelian r ↥V ∧ Nat.card ↥V = r ^ 2 ∧
    (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) ∧ Odd (Nat.card ↥Z) ∧ Nat.Coprime (Nat.card ↥Z) r ∧ Z ≠ ⊥ ∧
    (∀ v ∈ V, ∀ z ∈ Z, v * z = z * v)

@[expose] def NoN2 (Y : Type) [Group Y] : Prop :=
  ∀ (r : ℕ) (V Z : Subgroup (MulAut Y)), ¬ N2Cfg Y r V Z

end CFSG.GH74.GLS.Stage2.Bender.Thm1
