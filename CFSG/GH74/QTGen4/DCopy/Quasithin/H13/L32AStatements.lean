module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32ANotation

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

@[expose] def Thm14_7_63_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp147 G T L V →
    L32A.IsHz T L V (L32A.hz T V) ∧ (∀ H : Subgroup G, L32A.IsHz T L V H → H = L32A.hz T V) ∧
    L32A.hz T V = L32A.kz T V ⊔ T ∧ quasithinIsCComponent (L32A.kz T V) (L32A.hz T V) ∧
    quasithinO2QuotientIso (L32A.hz T V) (Equiv.Perm (Fin 5)) ∧
    IsIndecOnSection (L32A.kz T V) (fsuU T V) (fsuV1 T V) ∧
    ∃ U₀ : Subgroup G, (∀ u : G, u ∈ U₀ ↔ u ∈ fsuU T V ∧
        ∀ k ∈ L32A.kz T V, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) ∧
      L32A.IsL24Section (L32A.kz T V) (fsuU T V) U₀

end CFSG.Quasithin.H13
