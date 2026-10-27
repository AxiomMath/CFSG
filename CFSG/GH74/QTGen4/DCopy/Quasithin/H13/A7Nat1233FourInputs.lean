module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A7Nat1233FourInputs

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup

@[expose] def Insp1233Mod_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V),
    Setting1233Four hyp → ∀ z : G, z ∈ V → z ≠ 1 → z ∈ quasithinOmegaOneCenter T →
      (∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, v = l * z * l⁻¹) ∧
      pCoreOf 2 (autOn (hyp.Lv z ⊔ hyp.Tv z) V) = ⊥ ∧
      autOn (hyp.Lv z) V = perfectCore (autOn (hyp.Lv z) V) ∧
      V = ⁅V, hyp.Lv z⁆ ∧
      quasithinIsFaithfulLocal T (Kv hyp z)

@[expose] def Insp1233K_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V),
    Setting1233Four hyp → ∀ z : G, z ∈ V → z ≠ 1 → z ∈ quasithinOmegaOneCenter T →
      HypC28 (hyp.Gv z) hyp.Q (hyp.Mv z) (Kv hyp z) V →
      ∀ K : Subgroup G, K ∈ cComp (hyp.Gv z) → Kv hyp z ≤ K → Kv hyp z = K

end CFSG.Quasithin.H13.A7
