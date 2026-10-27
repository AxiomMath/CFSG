module

public import CFSG.GH74.AS16.E2.Basic

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

@[expose] def S_ALSS3121E2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.GH74.E2.Hyp G → Assembly.evenRank G ≤ 2 →
    Assembly.Quasithin.quasithinEvenCharacteristic G

@[expose] def NoPairOf (P : (K : Type) → [Group K] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (z : G) (L : Subgroup G),
    Cfg G T z L → GLS.IsTerminalPair 2 z L → P ↥L → False

@[expose] def NoPairA5NT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (z : G) (L : Subgroup G),
    Cfg G T z L → ShapeA5 ↥L → ¬ Terminal L → False

structure E2Leaves : Prop where
  a5nt : NoPairA5NT
  l28 : NoPairOf ShapeL28
  l33 : NoPairOf ShapeL33
  u33 : NoPairOf ShapeU33
  sz8 : NoPairOf ShapeSz8
  m11 : NoPairOf ShapeM11
  m12c : NoPairOf Shape2M12
  sz8c : NoPairOf Shape2Sz8

end CFSG.GH74.AS16.E2
