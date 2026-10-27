module

public import CFSG.GF2Type.Aschbacher1976Full.Defs
public import CFSG.GF2Type.CenterFour.Setting
public import CFSG.GF2Type.Aschbacher1976Common.CyclicTICommute
public import CFSG.Quasithin.Recognition.HSTypeDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

@[expose] def HSSetting (G : Type) [Group G] [Finite G] (z : G) : Prop :=
  Asc76Setting G z ∧ IsZ4Star z 2

abbrev ZF (u : G) : Subgroup G := CFSG.GF2Type.CenterFour.centerAt u

@[expose] def Dinv (z : G) : Set G :=
  {u | IsConj z u ∧ u ≠ z ∧ ZF u ≤ Hz z}

@[expose] def HSTI (z : G) : Prop :=
  (Dinv z).Nonempty ∧ ∀ u ∈ Dinv z, u ∈ Fz z ∧ ∀ y : G, ZF u = Subgroup.zpowers y → y ∉ Fz z

@[expose] def WT (T : Subgroup G) (z : G) : Subgroup G :=
  ⨆ B ∈ CFSG.GF2Type.Aschbacher1976Common.conjugatesIn (ZF z) T, B

@[expose] def ET (T : Subgroup G) (z : G) : Subgroup G :=
  Subgroup.closure {v : G | IsConj z v ∧ ZF v ≤ T}

@[expose] def HSWide (z : G) : Prop :=
  ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Hz z ∧ Nat.card (ET (T : Subgroup G) z) = 8 ∧
    Nat.card (WT (T : Subgroup G) z) = 64

@[expose] def HSS5 (z : G) : Prop :=
  ∃ φ : ↥(Hz z) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
    φ.ker = (Fz z).subgroupOf (Hz z)

@[expose] def HSPartA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HSSetting G z → HSTI z

@[expose] def HSBadCfg (z : G) : Prop :=
  ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Hz z ∧ Nat.card (ET (T : Subgroup G) z) = 4

@[expose] def HSTransCfg (z : G) : Prop :=
  ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Hz z ∧ Nat.card (ET (T : Subgroup G) z) = 8 ∧
    Nat.card (WT (T : Subgroup G) z) ≠ 64

@[expose] def HSPartCard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HSSetting G z → HSTI z →
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Hz z ∧
      (Nat.card (ET (T : Subgroup G) z) = 4 ∨ Nat.card (ET (T : Subgroup G) z) = 8)

@[expose] def HSPartBad : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HSSetting G z → HSTI z → ¬ HSBadCfg z

@[expose] def HSPartTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HSSetting G z → HSTI z → ¬ HSTransCfg z

@[expose] def HSPartW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HSSetting G z → HSTI z → HSWide z

@[expose] def HSPartC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HSSetting G z → HSTI z → HSWide z → HSS5 z

@[expose] def HSPartE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), HSSetting G z → HSTI z → HSWide z → HSS5 z →
    CFSG.Quasithin.HSType.IsTypeHS G

end CFSG.GF2Type.Aschbacher1976Full.HS
