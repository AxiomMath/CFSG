module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CF81L2Cent2Nilp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p (2 * f) → ∀ y₀ : Y, orderOf y₀ = 2 →
      HasNormalPComplement 2 ↥(centralizer ({MulAut.conj y₀} : Set (MulAut Y)))

end CFSG.ComponentClassification.GSThmB
