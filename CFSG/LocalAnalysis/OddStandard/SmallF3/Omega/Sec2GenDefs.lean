module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Mat2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def GenPocket {P : Type} [Group P] (zb : P) (K R : Subgroup P) : Prop :=
  Sl23PocketIn (⊤ : Subgroup P) zb K ∧ Nonempty (↥K ≃* SL2F3) ∧ R ≤ K ∧
    (R.subgroupOf K).Normal ∧ IsPGroup 2 ↥R

@[expose] def genPocketCore {P : Type} [Group P] (zb : P) : Subgroup P :=
  ⨆ (K : Subgroup P) (R : Subgroup P) (_ : GenPocket zb K R), R

@[expose] def NotQuat {P : Type} [Group P] (d : P) : Prop :=
  ∀ f : QuaternionGroup 2 →* P, Function.Injective f → f (QuaternionGroup.a 2) ≠ d

@[expose] def GenGood {P : Type} [Group P] (zb d : P) (X : Subgroup P) : Prop :=
  d ≠ 1 ∧ d * d = 1 ∧ d ∈ genPocketCore zb ∧ NotQuat d ∧
    IsComponentIn X (centralizer ({d} : Set P)) ∧ d ∈ X ∧ IsTwoU43 ↥X

@[expose] def genLayers {P : Type} [Group P] (zb : P) : Subgroup P :=
  ⨆ (d : P) (X : Subgroup P) (_ : GenGood zb d X), X

@[expose] def GenP {P : Type} [Group P] (zb : P) : Prop :=
  (⊤ : Subgroup P) ≤ genLayers zb

end CFSG.OddStandard.SmallF3.Omega
