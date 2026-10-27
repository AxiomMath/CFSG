module

public import CFSG.GH74.Generic.S45.L1310

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.GH74.Uniqueness.Bender

@[expose] def B_III11_13_10_g4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Gen4 K → InCalK2 K →
    ∀ y : MulAut K, orderOf y = 2 →
      ∀ L : Subgroup K, L ≤ fixSub (zpowers y) →
        (L.subgroupOf (fixSub (zpowers y))).IsSubnormal → HasL2Model ↥L Odd →
        (∀ P : Sylow 2 ↥(fixSub (zpowers y)), IsElementaryAbelian 2 ↥(P : Subgroup ↥(fixSub (zpowers y)))) →
        (¬ ∃ f : ℕ, LieModel K .twistedG2 0 3 f) →
        (HasL2Model ↥L (fun q => q = 5) → ¬ NativeSporadic.IsSporadic K .J1) →
        HasL2Model ↥L (fun q => q = 5) ∧ IsPumpOutcome K ∧
          (¬ NativeSporadic.IsSporadic K .J2 → y ∉ (MulAut.conj : K →* MulAut K).range)

@[expose] def Hyp1310g (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K) : Prop :=
  Gen4 K ∧ Hyp1310 K y L

@[expose] def SporRowG (s : TauCeti.SporadicName) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    NativeSporadic.IsSporadic (K ⧸ center K) s → False

@[expose] def B_1310_spor_g4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    (∃ s : TauCeti.SporadicName, NativeSporadic.IsSporadic (K ⧸ center K) s) → Concl1310 K y L

end CFSG.GH74.Generic.S45
