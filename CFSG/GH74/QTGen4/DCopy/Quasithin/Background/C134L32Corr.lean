module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.C41PfCorr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def C134L32Corr_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)), Fintype.card F = 2 ∧ IsModO2Surj L α) →
      ∃ i : ℕ, C134CorrLocal.IsC134CaseCorr i G₀ R L

end CFSG.Quasithin
