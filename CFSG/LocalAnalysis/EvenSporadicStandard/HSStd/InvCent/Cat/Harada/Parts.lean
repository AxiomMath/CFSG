module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.TwoCfg

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def NoZ2S5 (P : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal → P ↥S →
    centralizer (S : Set G) = ⊥ → ∀ t : G, orderOf t = 2 → centralizerDerived t ≤ S →
    ¬ Nonempty (↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))

@[expose] def NoTwoCfg (P : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal → P ↥S →
    centralizer (S : Set G) = ⊥ → ∀ (t v : G) (J : Subgroup G), TwoCfg t v J →
    centralizerDerived t ≤ S → False

@[expose] def NoZ2S5L216 : Prop := NoZ2S5 fun S _ => LieModel S .PSL 2 2 4

@[expose] def NoZ2S5U34 : Prop := NoZ2S5 fun S _ => LieModel S .PSU 3 2 2

@[expose] def NoZ2S5PSp45 : Prop := NoZ2S5 fun S _ => LieModel S .PSp 2 5 1

@[expose] def NoZ2S5J1 : Prop := NoZ2S5 fun S _ => Nonempty (S ≃* Carrier .J1)

@[expose] def NoZ2S5J2 : Prop := NoZ2S5 fun S _ => Nonempty (S ≃* Carrier .J2)

@[expose] def HaradaM12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal → Nonempty (↥S ≃* Carrier .M12) →
    centralizer (S : Set G) = ⊥ → ∀ t : G, orderOf t = 2 →
    Nonempty (↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) →
    S = ⊤

@[expose] def NoTwoCfgL216 : Prop := NoTwoCfg fun S _ => LieModel S .PSL 2 2 4

@[expose] def NoTwoCfgL34 : Prop := NoTwoCfg fun S _ => LieModel S .PSL 3 2 2

@[expose] def NoTwoCfgU34 : Prop := NoTwoCfg fun S _ => LieModel S .PSU 3 2 2

@[expose] def NoTwoCfgL225 : Prop := NoTwoCfg fun S _ => LieModel S .PSL 2 5 2

@[expose] def NoTwoCfgL35 : Prop := NoTwoCfg fun S _ => LieModel S .PSL 3 5 1

@[expose] def NoTwoCfgU35 : Prop := NoTwoCfg fun S _ => LieModel S .PSU 3 5 1

@[expose] def NoTwoCfgPSp45 : Prop := NoTwoCfg fun S _ => LieModel S .PSp 2 5 1

@[expose] def NoTwoCfgJ1 : Prop := NoTwoCfg fun S _ => Nonempty (S ≃* Carrier .J1)

@[expose] def NoTwoCfgJ2 : Prop := NoTwoCfg fun S _ => Nonempty (S ≃* Carrier .J2)

@[expose] def NoTwoCfgM12 : Prop := NoTwoCfg fun S _ => Nonempty (S ≃* Carrier .M12)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
