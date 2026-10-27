module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_18_DL_outer_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_14 G T M L V H B D n → Even n →
      ∀ D₃ : Subgroup G, D₃ ≤ D → Nat.card D₃ = 3 →
        D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
        (∃ d ∈ D₃, ∀ k ∈ oTwoUpper H, d * k⁻¹ ∉ centralizerModO2 (oTwoUpper H)) →
          ¬ D ≤ Subgroup.normalizer (oTwoUpper H : Set G)

end CFSG.Quasithin.H13
