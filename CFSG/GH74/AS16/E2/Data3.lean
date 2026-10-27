module

public import CFSG.GH74.AS16.E2.Delta3

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp
open CFSG.GH74.Uniqueness (S_CorZD)

@[expose] def NoPairL33Outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (z : G) (L : Subgroup G),
    Cfg G T z L → GLS.IsTerminalPair 2 z L → ShapeL33 ↥L →
      ¬ InnerAction (T : Subgroup G) L → False

theorem noPairM11_of_delta (hZD : S_CorZD) (hD3 : K0Data3) (hS : SmallData ShapeM11)
    (hO : OutTrivial ShapeM11) (hT3 : Local3Data ShapeM11) : NoPairOf ShapeM11 := by
  intro G _ _ T z L hcfg hterm hsh
  have hZ : center ↥L = ⊥ :=
    hD3.center_bot ↥L (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsh)))))
  have hinn := hcfg.innerAction_of_out (hO ↥L hsh)
  have hL3 : Local3Sub L :=
    Local3Sub.of_table (hT3 ↥L hsh) (hD3.inner3 ↥L (Or.inr (Or.inr hsh)))
  have hcard := hcfg.card_tC_eq_two hZD hterm hZ hL3 hinn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact noPairM11_of_cyclic hD3 hS hO hcfg hsh (isCyclic_of_prime_card hcard)

theorem noPairL33_of_delta (hZD : S_CorZD) (hD3 : K0Data3) (hS : SmallData ShapeL33)
    (hT3 : Local3Data ShapeL33) (h : NoPairL33Outer) : NoPairOf ShapeL33 := by
  intro G _ _ T z L hcfg hterm hsh
  by_cases hinn : InnerAction (T : Subgroup G) L
  · have hZ : center ↥L = ⊥ := hD3.center_bot ↥L (Or.inr (Or.inr (Or.inr (Or.inl hsh))))
    have hL3 : Local3Sub L :=
      Local3Sub.of_table (hT3 ↥L hsh) (hD3.inner3 ↥L (Or.inr (Or.inl hsh)))
    have hcard := hcfg.card_tC_eq_two hZD hterm hZ hL3 hinn
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact noPairL33_of_cyclic_inner hD3 hS hcfg hsh hinn (isCyclic_of_prime_card hcard)
  · exact h G T z L hcfg hterm hsh hinn

end CFSG.GH74.AS16.E2
