module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_47_L32Mod_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (L32A.l1 T L V ⊔ T) → IsPSL 3 2 1 (L32A.cStar K) →
      ¬ L32A.l1 T L V ≤ K →
      (∀ x ∈ L32A.l1 T L V, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
      ∀ t ∈ T, (∀ k ∈ K, ∃ x ∈ K, t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∉ pCoreOf 2 K) → False

end CFSG.Quasithin.H13.L32A.C
