module

public import CFSG.GF2Type.Aschbacher1976Full.HSDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

@[expose] def BadCruxStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSTI z →
    ∀ (T : Sylow 2 G), (T : Subgroup G) ≤ Hz z → Nat.card (ET (T : Subgroup G) z) = 4 →
    ∀ k : G, ZF z = Subgroup.zpowers k →
      k ∉ ⁅(T : Subgroup G), (T : Subgroup G)⁆ ⊔
        Subgroup.closure {u : G | u ∈ (T : Subgroup G) ∧ IsConj z u ∧ u * k = k * u}

end CFSG.GF2Type.Aschbacher1976Full.HS
